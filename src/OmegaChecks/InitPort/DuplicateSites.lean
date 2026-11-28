import OmegaChecks.Interface

open Lean

private def portName (n : Name) := if OmegaChecks.InitCompiler.RootNames.usesRoot n then n else `Omega ++ n

private abbrev ModuleGraph := NameMap (Array Name)

private def reachable (graph : ModuleGraph) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  while let some n := todo.back? do
    todo := todo.pop
    unless seen.contains n do
      seen := seen.insert n
      todo := todo ++ graph.getD n #[]
  return seen

/-- Independent modules can generate the same theorem with different proofs.
Each defining site must expose the same proposition and binders. -/
private def duplicateSites (strict source surface : Environment) : IO (NameMap (Array Name)) := do
  let mut sites : NameMap (Array Name) := {}
  for (owner, data) in surface.header.moduleNames.zip surface.header.moduleData do
    for n in data.constNames do
      if !isPrivateName n && !n.isInternal && strict.contains (portName n) then
        sites := sites.insert n ((sites.getD n #[]).push owner)
  let mut copies : NameMap (Array Name) := {}
  for (n, owners) in sites.toList do
    if owners.size < 2 || !owners.all (OmegaChecks.Interface.declaredIn source n ·) then continue
    let target := portName n
    let some idx := strict.getModuleIdxFor? target | continue
    let origin := strict.header.moduleNames[idx]!.replacePrefix `OmegaInit `Init
    unless OmegaChecks.Interface.declaredIn source n origin do continue
    for official in owners do
      let port := official.replacePrefix `Init `OmegaInit
      let some idx := strict.getModuleIdx? port | continue
      if strict.header.moduleData[idx]!.constNames.contains target then continue
      unless (strict.find? target).any (· matches .thmInfo _) &&
          (source.find? n).any (· matches .thmInfo _) do
        throw <| IO.userError s!"unsupported repeated declaration kind for {n} in {official}"
      copies := copies.insert port ((copies.getD port #[]).push target)
  return copies

private def copyImports (strict : Environment) (graph : ModuleGraph)
    (copies : NameMap (Array Name)) (owner : Name) (names : Array Name) : IO (Array Name) := do
  let mut available := reachable graph owner
  let mut extra := #[]
  for name in names do
    let some info := strict.find? name | throw <| IO.userError s!"missing strict theorem {name}"
    for dep in info.getUsedConstantsAsSet do
      let some idx := strict.getModuleIdxFor? dep | throw <| IO.userError s!"missing dependency {dep}"
      let provider := strict.header.moduleNames[idx]!
      if available.contains provider || available.toList.any (fun m => (copies.getD m #[]).contains dep)
        then continue
      let candidates := #[provider] ++ (copies.toList.filterMap fun (m, ns) => if ns.contains dep then some m else none).toArray
      let some imported := candidates.find? (fun m => !(reachable graph m).contains owner)
        | throw <| IO.userError s!"no acyclic provider for {dep} in {owner}"
      extra := extra.push imported
      available := available ++ reachable graph imported
  return extra

private def copyModule (dir : System.FilePath) (strict source : Environment)
    (owner : Name) (names imports : Array Name) : IO Unit := do
  let file := modToFilePath dir owner "olean"
  let files := #[file, file.addExtension "server", file.addExtension "private"]
  let parts ← readModuleDataParts files
  let upstream := owner.replacePrefix `OmegaInit `Init
  let origin := modToFilePath (← getLibDir (← findSysroot)) upstream "olean"
  let views ← readModuleDataParts #[origin, origin.addExtension "server", origin.addExtension "private"]
  let mut entries := (← mkEmptyEnvironment).setMainModule owner
  for n in protectedExt.getModuleEntries strict (strict.getModuleIdx? owner).get! do
    entries := addProtected entries n
  for n in names do
    if isProtected source (n.replacePrefix `Omega .anonymous) then entries := addProtected entries n
  let protectedEntries := (← mkModuleData entries).entries.filter (·.1 == protectedExt.name)
  let mut output := #[]
  for (part, _) in parts, (view, _) in views, path in files, level in #[OLeanLevel.exported, .server, .private] do
    let mut aliases := (← mkEmptyEnvironment).setMainModule owner
    for entry in aliasExtension.getModuleEntries strict (strict.getModuleIdx? owner).get! (level := level) do
      aliases := aliasExtension.addEntry aliases entry
    let mut constants := part.constants
    for n in names do
      let original := n.replacePrefix `Omega .anonymous
      let some upstream := view.constants.find? (·.name == original) | continue
      let some ci := strict.find? n | throw <| IO.userError s!"missing strict proof of {n}"
      if let some entry := OmegaChecks.InitCompiler.RootNames.aliasFor? original then
        if entry.2 == n then aliases := aliasExtension.addEntry aliases entry
      constants := constants.push <| if upstream.isAxiom then
        .axiomInfo {ci.toConstantVal with isUnsafe := false} else ci
    constants := constants.qsort fun a b => Name.quickLt a.name b.name
    let edges := part.imports ++ imports.map fun n => {module := n, isExported := false}
    let aliasEntries := (← mkModuleData aliases .private).entries.filter (·.1 == aliasExtension.name)
    let data := { part with
      constants
      constNames := constants.map (·.name)
      imports := edges
      entries := part.entries.filter (fun e => e.1 != protectedExt.name && e.1 != aliasExtension.name) ++ protectedEntries ++ aliasEntries }
    output := output.push (path, data)
  saveModuleDataParts owner output

/-- Check the relocated proofs using only imports available at their destination. -/
private def checkCopies (owner : Name) (names : Array Name) : IO Unit := do
  let imports := #[{module := owner : Import}]
  let localEnv ← importModules imports {}
  let visible ← importModules imports {} (level := .exported)
  let idx := (visible.getModuleIdx? owner).get!
  for n in names do
    unless visible.header.moduleData[idx]!.constNames.contains n &&
        OmegaChecks.Interface.declaredIn localEnv n owner do
      throw <| IO.userError s!"missing exported definition of {n} in {owner}"
    let home := (localEnv.getModuleIdx? owner).get!
    let some (.thmInfo thm) := localEnv.header.moduleData[home]!.constants.find? (·.name == n)
      | throw <| IO.userError s!"missing local proof of {n} in {owner}"
    let .ok inferred := Kernel.check localEnv {} thm.value
      | throw <| IO.userError s!"could not kernel-check the local proof of {n} in {owner}"
    unless Kernel.isDefEqGuarded localEnv {} inferred thm.type do
      throw <| IO.userError s!"local proof type mismatch for {n} in {owner}"

def main (args : List String) : IO Unit := do
  let [directory] := args | throw <| IO.userError "expected the generated product directory"
  let product := System.FilePath.mk directory
  let path := product / "modules.json"
  let rows : Array (Name × Array Name) ← IO.ofExcept <| (← Json.parse <$> IO.FS.readFile path) >>= fromJson?
  let mut graph : ModuleGraph := {}
  for (owner, imports) in rows do graph := graph.insert owner imports
  let modules := rows.map Prod.fst
  let dir := product / "lib"
  searchPathRef.set [dir]
  let strict ← importModules (modules.map fun n => {module := n}) {}
  let official := modules.map fun n => {module := n.replacePrefix `OmegaInit `Init : Import}
  searchPathRef.set [← getLibDir (← findSysroot)]
  let source ← importModules official {}
  let surface ← importModules official {} (level := .exported)
  let copies ← duplicateSites strict source surface
  let mut count := 0
  for (owner, names) in copies.toList do
    let imports ← copyImports strict graph copies owner names
    copyModule dir strict source owner names imports
    graph := graph.insert owner (graph.getD owner #[] ++ imports)
    count := count + names.size
  searchPathRef.set [dir]
  for (owner, names) in copies.toList do checkCopies owner names
  IO.FS.writeFile path <| (toJson (modules.map fun n => (n, graph.getD n #[]))).compress
  IO.println s!"Distributed and kernel-checked {count} public theorem occurrences in {copies.size} official modules."
