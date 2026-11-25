import Lean
open Lean

def officialModuleName (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  return env.header.moduleNames[i]!

def renamed (src : Environment) (n : Name) : Name :=
  if let some usr := privateToUserName? n then
    let m := (officialModuleName src n).getD .anonymous
    mkPrivateNameCore (m.replacePrefix `Init `OmegaInit) (`Omega ++ usr)
  else `Omega ++ n

def declarationDependencies (ci : ConstantInfo) : NameSet := Id.run do
  let mut deps := ci.getUsedConstantsAsSet
  match ci with
  | .inductInfo i =>
    for n in i.all do deps := (deps.insert n).insert (n ++ `rec)
  | .ctorInfo c => deps := deps.insert c.induct
  | .recInfo r =>
    for caseRule in r.rules do deps := (deps.insert caseRule.ctor) ++ caseRule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return deps

def readLevels (f : System.FilePath) : IO (Array ModuleData) := do
  if !(← f.pathExists) then return Array.replicate 3 default
  let xs ← readModuleDataParts #[f, f.addExtension "server", f.addExtension "private"]
  return xs.map (·.1)

def mergeImports (a b : Array Import) : Array Import := Id.run do
  let mut out := a
  for i in b do
    if !(out.contains i) then out := out.push i
  return out

def main (args : List String) : IO Unit := do
  let lib :: seed :: out :: roots := args | throw <| IO.userError "expected transfer, seed, output and official roots"
  let lib := System.FilePath.mk lib
  let seed := System.FilePath.mk seed
  let out := System.FilePath.mk out
  let toolchain ← getLibDir (← findSysroot)
  let mods := roots.toArray.map String.toName
  searchPathRef.set [toolchain]
  let imports := mods.map fun n => {module := n : Import}
  let source ← importModules imports {} (level := .private)
  let owners := source.header.moduleNames.filter (fun m => m.getRoot == `Init)
  let surface ← importModules (owners.map fun n => {module := n}) {} (level := .exported)
  searchPathRef.set [lib, seed]
  let monolith ← importModules #[{module := `OmegaImported}] {}
  let newDecls := monolith.header.moduleData[(monolith.getModuleIdx? `OmegaImported).get!]!
  let mut reverseNames : Std.HashMap Name Name := {}
  for (n, _) in source.constants.toList do reverseNames := reverseNames.insert (renamed source n) n
  let mut groups : NameMap (Array (Name × ConstantInfo)) := {}
  for ci in newDecls.constants do
    let some upstream := reverseNames[ci.name]? | throw <| IO.userError s!"no official name for {ci.name}"
    let owner := (officialModuleName source upstream).get!
    groups := groups.insert owner ((groups.getD owner #[]).push (upstream,ci))
  IO.FS.createDirAll out
  let mut graph := #[]
  let edgeInfo ← IO.FS.Handle.mk (out.parent.get!.parent.get! / "candidate-edges.jsonl") .write
  let mut count := 0
  let mut kept := 0
  let mut keptOwners := 0
  for official in owners do
    let owner := official.replacePrefix `Init `OmegaInit
    let srcPath := modToFilePath seed owner "olean"
    let orig ← readLevels srcPath
    let idx := (source.getModuleIdx? official).get!
    let mut mappedImports := (source.header.moduleData[idx]!.imports.filter (·.isExported)).map fun i =>
      { i with module := i.module.replacePrefix `Init `OmegaInit }
    let baseImports := mergeImports orig[2]!.imports mappedImports
    edgeInfo.putStrLn (toJson #[owner.toString, "",(toJson (baseImports.map (·.module.toString))).compress]).compress
    let exported := surface.header.moduleData[(surface.getModuleIdx? official).get!]!
    let publiclyDeclared : NameMap ConstantInfo := exported.constants.foldl (fun acc ci => acc.insert ci.name ci) {}
    let group := groups.getD official #[]
    kept := kept + group.size
    if !group.isEmpty then keptOwners := keptOwners + 1
    for (originalName, ci) in group do
      let mut edges := #[]
      let deps := (declarationDependencies ci).toArray
      for dep in deps do
        if let some up := reverseNames[dep]? then
          if let some m := officialModuleName source up then
            let target := m.replacePrefix `Init `OmegaInit
            if target != owner && !(baseImports.any (·.module == target)) then
              if !edges.contains target then edges := edges.push target
              if !(mappedImports.any (·.module == target)) then
                mappedImports := mappedImports.push {module := target, isExported := false}
      if !edges.isEmpty then edgeInfo.putStrLn (toJson #[owner.toString, originalName.toString, (toJson (edges.map Name.toString)).compress]).compress
    for i in mappedImports do
      unless i.module.getRoot == `OmegaInit do throw <| IO.userError s!"{owner} import {i.module}"
    let path := modToFilePath out owner "olean"
    IO.FS.createDirAll path.parent.get!
    let mut parts := #[]
    let mut metadata := (← mkEmptyEnvironment).setMainModule owner
    if let some old := monolith.getModuleIdx? owner then
      for cls in classExtension.getModuleEntries monolith old do metadata := classExtension.addEntry metadata cls
      for key in protectedExt.getModuleEntries monolith old do metadata := addProtected metadata key
      for e in reducibilityCoreExt.getModuleEntries monolith old do metadata := reducibilityCoreExt.addEntry (asyncDecl := e.1) metadata e
    let sourceNames := NameSet.ofList (group.toList.map Prod.fst)
    for cls in classExtension.getModuleEntries surface (surface.getModuleIdx? official).get! do
      if sourceNames.contains cls.name then metadata := classExtension.addEntry metadata {cls with name := renamed source cls.name}
    for (n, ci) in group do
      if isProtected source n then metadata := addProtected metadata ci.name
      let status := if (publiclyDeclared.find? n).any (·.isAxiom) && ci matches .defnInfo _ then .irreducible else getReducibilityStatusCore source n
      if status != .semireducible then metadata := reducibilityCoreExt.addEntry (asyncDecl := ci.name) metadata (ci.name, status)
    let withMetadata ← mkModuleData metadata
    let selected := #[classExtension.name, protectedExt.name, reducibilityCoreExt.name]
    let replacement := withMetadata.entries.filter (fun e => selected.contains e.1 && !e.2.isEmpty)
    for i in [:3] do
      let previous := orig[i]!
      let mut cs := previous.constants
      for (n,new) in group do
        if i == 2 then cs := cs.push new
        else if let some exposed := publiclyDeclared.find? n then
          if exposed.isAxiom && !new.isAxiom then
            let hidden := ConstantInfo.axiomInfo {new.toConstantVal with isUnsafe := false}
            cs := cs.push hidden
          else cs := cs.push new
      cs := cs.qsort fun a b => a.name.quickCmp b.name == .lt
      let entries := (previous.entries.filter (fun e => !selected.contains e.1)) ++ replacement
      let data : ModuleData := { previous with entries, isModule := true, imports := mergeImports previous.imports mappedImports, constants := cs, constNames := cs.map (·.name) }
      parts := parts.push (#[path,path.addExtension "server",path.addExtension "private"][i]!,data)
    graph := graph.push (owner.toString, (mergeImports orig[2]!.imports mappedImports).map (·.module.toString))
    saveModuleDataParts owner parts
    let iseed := srcPath.withExtension "ir"
    if ← iseed.pathExists then
      IO.FS.writeBinFile (path.withExtension "ir") (← IO.FS.readBinFile iseed)
      IO.FS.writeBinFile (path.withExtension "ir.sig") (← IO.FS.readBinFile (iseed.addExtension "sig"))
    else
      let ir : ModuleData := { (default : ModuleData) with isModule := true, imports := mappedImports }
      saveModuleDataParts (owner ++ `ir) #[(path.withExtension "ir.sig", default),(path.withExtension "ir",ir)]
    count := count + 1
  let mut copied := NameSet.ofList (owners.toList.map (fun n => n.replacePrefix `Init `OmegaInit))
  let mut pending := graph.flatMap Prod.snd
  while let some dep := pending.back? do
    pending := pending.pop
    let name := dep.toName
    unless copied.contains name do
      let path := modToFilePath seed name "olean"
      unless ← path.pathExists do throw <| IO.userError s!"missing seed dependency {name}"
      let original ← readLevels path
      let imports := original[2]!.imports.map (·.module.toString)
      graph := graph.push (dep, imports)
      pending := pending ++ imports
      for ext in #["olean", "olean.server", "olean.private", "ir", "ir.sig"] do
        let to := modToFilePath out name ext
        IO.FS.createDirAll to.parent.get!
        IO.FS.writeBinFile to (← IO.FS.readBinFile (modToFilePath seed name ext))
      copied := copied.insert name
  IO.FS.writeFile (out.parent.get! / "modules.json") (toJson graph).compress
  IO.println s!"Wrote {count} modules and {kept} additions in {keptOwners} owners."
