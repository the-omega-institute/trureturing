import Lean
open Lean

def officialModuleName (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  return env.header.moduleNames[i]!

def renamed (n : Name) : Name :=
  if let some user := privateToUserName? n then
    if let some lexical := privatePrefix? n then
      if (`_private.Init).isPrefixOf lexical && isPrivatePrefix lexical then
        lexical.replacePrefix `_private.Init `_private.OmegaInit ++ (`Omega ++ user)
      else `Omega ++ n
    else `Omega ++ n
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

/-- Replay the official candidate order, including scoped instances and priority ties.
Only publish entries whose implementation is available at this definition site. -/
private def instanceEntries (source : Environment) (idx : ModuleIdx) (available : NameSet)
    (owner : Name) (level : OLeanLevel) : IO (Array (Name × Array EnvExtensionEntry)) := do
  let mut env := (← mkEmptyEnvironment).setMainModule owner
  let ext := Meta.instanceExtension
  for entry in ext.ext.getModuleEntries source idx (level := level) do
    let (scope, v) := match entry with
      | .global v => (none, v)
      | .scoped ns v => (some ns, v)
    let some n := v.globalName? | throw <| IO.userError s!"unnamed exported instance in {owner}"
    let port := renamed n
    unless available.contains port do continue
    let .const decl us := v.val | throw <| IO.userError s!"invalid instance {n}"
    unless decl == n do throw <| IO.userError s!"inconsistent instance name {n}"
    let keys := v.keys.map fun k => match k with
      | .const name arity => .const (renamed name) arity
      | .proj name i arity => .proj (renamed name) i arity
      | k => k
    let translated := {v with val := .const port us, keys, globalName? := some port}
    env := match scope with
      | some ns => ext.addScopedEntry env (renamed ns) translated
      | none => ext.addEntry env translated
  return (← mkModuleData env level).entries.filter (·.1 == ext.ext.name)

/-- Definitions with pointwise computation equations checked by the interface audit. -/
private def sealedImplementation (n : Name) : Bool :=
  [`Fin.natAdd, `Option.isNone, `Array.modifyMUnsafe,
    `Quot.hrecOn, `ByteArray.fastAppend, `String.utf8EncodeCharFast, `Char.succ?, `Std.Iter.Total.atIdxSlow?, `Std.IterM.Total.toArray, `Std.IterM.Total.toListRev, `Std.Iterators.Types.Take.Rel,
    `instSliceSizeListSliceData, `List.instAppendListSlice,
    `List.instToStringListSlice, `instIteratorLoopSubarrayIteratorIdOfMonad,
    `Std.Iterators.Types.ListIterator.instIteratorLoop,
    `String.Slice.ByteIterator.instIteratorLoopUInt8OfMonad,
    `String.Slice.Pattern.ForwardSliceSearcher.instIteratorLoopIdSearchStep,
    `String.Slice.PosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad,
    `Std.Rxc.Iterator.instIteratorLoop.loop, `Std.Rxo.Iterator.instIteratorLoop,
    `List.appendTR, `List.lengthTR, `List.mapTR, `List.filterTR, `List.filterMapTR, `List.replicateTR, `List.leftpadTR, `List.range'TR, `List.intersperseTR,
    `Array.instDecidableEq, `Lean.RArray.getImpl,
    `String.Slice.RevByteIterator.instIteratorLoopUInt8OfMonad,
    `String.Slice.RevByteIterator.instForInCharOfMonad,
    `String.Slice.RevPosIterator.instIteratorLoopSubtypePosNeEndPosOfMonad].contains n

/-- Inline a later proof dependency locally, so module cycles do not discard checked
theorems. Types, owners and computational declarations stay as translated by the kernel. -/
private def localizeProof (env : Environment) (later : Name → Bool) (ci : ConstantInfo) :
    IO ConstantInfo := do
  let .thmInfo thm := ci | return ci
  unless thm.value.getUsedConstantsAsSet.any later do return ci
  if thm.type.getUsedConstantsAsSet.any later then return ci
  let expand := fun n => later n && (env.find? n).any (fun c => c.isTheorem || c matches .defnInfo _)
  let work := Meta.deltaExpand thm.value expand (allowOpaque := true)
  let context : Core.Context := { fileName := "<module-local proof>", fileMap := default }
  match ← (work.toIO {context with options := maxHeartbeats.set context.options 20000} {env}).toBaseIO with
  | .ok (body, _) =>
    if body.getUsedConstantsAsSet.any later then return ci
    return .thmInfo {thm with value := body}
  | .error _ => return ci

def main (args : List String) : IO Unit := do
  let (order, args) ← match args with
    | "--order" :: path :: rest => do
      let names : Array String ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile path))
      let mut order : NameMap Nat := {}
      for n in names, i in [:names.size] do order := order.insert n.toName i
      pure (order, rest)
    | _ => pure ({}, args)
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
  for (n, _) in source.constants.toList do reverseNames := reverseNames.insert (renamed n) n
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
    let officialImports := source.header.moduleData[idx]!.imports.map fun i =>
      (i.module.replacePrefix `Init `OmegaInit).toString
    edgeInfo.putStrLn (toJson #[owner.toString, "", (toJson (baseImports.map (·.module.toString))).compress,
      (toJson officialImports).compress]).compress
    let exported := surface.header.moduleData[(surface.getModuleIdx? official).get!]!
    let publiclyDeclared : NameMap ConstantInfo := exported.constants.foldl (fun acc ci => acc.insert ci.name ci) {}
    let mut group := groups.getD official #[]
    if let some rank := order.find? owner then
      let later := fun n => ((reverseNames[n]? >>= officialModuleName source).bind
        fun m => order.find? (m.replacePrefix `Init `OmegaInit)).any (· > rank)
      group ← group.mapM fun (n, ci) => return (n, ← localizeProof monolith later ci)
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
      if sourceNames.contains cls.name then metadata := classExtension.addEntry metadata {cls with name := renamed cls.name}
    for (n, ci) in group do
      if isProtected source n then metadata := addProtected metadata ci.name
      let status := if ((publiclyDeclared.find? n).any (·.isAxiom) || sealedImplementation n) && ci matches .defnInfo _ then .irreducible else getReducibilityStatusCore source n
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
          if (exposed.isAxiom || sealedImplementation n) && !new.isAxiom then
            let hidden := ConstantInfo.axiomInfo {new.toConstantVal with isUnsafe := false}
            cs := cs.push hidden
          else cs := cs.push new
      cs := cs.qsort fun a b => a.name.quickCmp b.name == .lt
      let level : OLeanLevel := match i with | 0 => .exported | 1 => .server | _ => .private
      let mut available := NameSet.ofList (cs.toList.map (·.name))
      if let some old := monolith.getModuleIdx? owner then
        for e in Meta.instanceExtension.ext.getModuleEntries monolith old (level := level) do
          let v := match e with | .global v | .scoped _ v => v
          if let some n := v.globalName? then available := available.insert n
      let instances ← instanceEntries source idx available owner level
      let entries := (previous.entries.filter (fun e =>
        !selected.contains e.1 && e.1 != Meta.instanceExtension.ext.name)) ++ replacement ++ instances
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
