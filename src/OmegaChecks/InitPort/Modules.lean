module
public import Lean
import OmegaChecks.InitPort.ReferenceSpecialization
meta import OmegaChecks.InitPort.ReferenceSpecialization
import OmegaChecks.InitPort.LawfulLoop
meta import OmegaChecks.InitPort.LawfulLoop
import OmegaChecks.InitPort.PatternMatch
meta import OmegaChecks.InitPort.PatternMatch
import OmegaChecks.InitPort.LogicalHandle
meta import OmegaChecks.InitPort.LogicalHandle
import OmegaChecks.InitCompiler.RootNames
meta import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitPort.TypeName
meta import OmegaChecks.InitPort.TypeName
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState
import all Lean.Structure

public section
open Lean

def officialModuleName (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  return env.header.moduleNames[i]!

def renamed (n : Name) : Name :=
  if OmegaChecks.InitCompiler.RootNames.usesRoot n then n
  else if let some user := privateToUserName? n then
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

/-- Copy the elaborator's declaration tags from the same visibility level as the constants. -/
private def elaboratorEntries (source visible seed : Environment) (idx : ModuleIdx) (owner : Name)
    (available : NameSet) (level : OLeanLevel) : IO (Array (Name × Array EnvExtensionEntry)) := do
  let mut env := (← mkEmptyEnvironment).setMainModule owner
  let names (original inherited : Array Name) :=
    NameSet.ofList (inherited ++ (original.map renamed).filter available.contains).toList
  for attr in #[matchPatternAttr, Elab.Term.elabAsElim, Meta.coeDeclAttr, neverExtractAttr] do
    let inherited := (seed.getModuleIdx? owner).map (fun old => attr.ext.getModuleEntries seed old (level := level))
    for name in names (attr.ext.getModuleEntries source idx (level := level)) (inherited.getD #[]) do
      env := attr.ext.addEntry (asyncDecl := name) env name
  let inherited := (seed.getModuleIdx? owner).map (fun old => auxRecExt.getModuleEntries seed old (level := level))
  -- Lean recognizes these auxiliary recursors by their root names as well as by tags.
  let builtin := #[`Eq.ndrec, `Eq.ndrec_symm, `Eq.ndrecOn].filter fun n =>
    source.getModuleIdxFor? n == some idx && isAuxRecursor source n
  let aux := auxRecExt.getModuleEntries source idx (level := level) ++ builtin
  for name in names aux (inherited.getD #[]) do
    env := markAuxRecursor env name
  let forOwner := fun t => source.getModuleIdxFor? t == some idx
  let mut aliases := #[]
  for target in source.header.moduleData[idx]!.constNames do
    if let some entry := OmegaChecks.InitCompiler.RootNames.aliasFor? target then
      if available.contains entry.2 then aliases := aliases.push entry
  for (alias, target) in aliasExtension.getModuleEntries source idx (level := level) do
    let port := renamed target
    if available.contains port || (!forOwner target && seed.contains port) then
      aliases := aliases.push (renamed alias, port)
  if let some old := seed.getModuleIdx? owner then
    for entry in aliasExtension.getModuleEntries seed old (level := level) do
      unless aliases.contains entry do aliases := aliases.push entry
  for entry in aliases do env := aliasExtension.addEntry env entry
  let matchers := Meta.Match.Extension.extension
  let mut inherited : NameSet := {}
  if let some old := seed.getModuleIdx? owner then
    for entry in matchers.getModuleEntries seed old (level := level) do
      inherited := inherited.insert entry.name
      env := Meta.Match.Extension.addMatcherInfo env entry.name entry.info
  -- MatcherInfo exports the same entries to ordinary and server imports.
  let matcherEnv := if level == .private then source else visible
  let matcherIdx := (matcherEnv.getModuleIdx? source.header.moduleNames[idx]!).get!
  for entry in matchers.getModuleEntries matcherEnv matcherIdx do
    let installed := renamed entry.name
    if !inherited.contains installed && available.contains installed && InitKernelPort.exactDefinition source seed.toKernelEnv entry.name then
      env := Meta.Match.Extension.addMatcherInfo env installed entry.info
  -- The empty encoder has no declarations. The two input entry arrays have already
  -- been filtered to this level, so export the assembled tags without filtering again.
  let data ← mkModuleData env .private
  return data.entries.filter fun e =>
    #[matchPatternAttr.ext.name, Elab.Term.elabAsElim.ext.name, Meta.coeDeclAttr.ext.name, neverExtractAttr.ext.name, auxRecExt.name, aliasExtension.name, matchers.name].contains e.1

/-- A structure literal needs its field order, inherited projections and binder information. -/
private def structureEntries (source port : Environment) (idx : ModuleIdx) (owner : Name)
    (available : NameSet) (level : OLeanLevel) : IO (Array (Name × Array EnvExtensionEntry)) := do
  let mut env := port.setMainModule owner
  if let some old := port.getModuleIdx? owner then
    for info in structureExt.getModuleEntries port old (level := level) do
      env := structureExt.addEntry env info
    for (name, info) in projectionFnInfoExt.getModuleEntries port old (level := level) do
      env := projectionFnInfoExt.addEntry (asyncDecl := name) env (name, info)
  for info in structureExt.getModuleEntries source idx (level := level) do
    let name := renamed info.structName
    unless available.contains name do continue
    let fields ← info.fieldInfo.mapM fun field => do
      if field.autoParam?.isSome then
        throw <| IO.userError s!"unexpected autoParam on {info.structName}.{field.fieldName}"
      return {field with projFn := renamed field.projFn, subobject? := field.subobject?.map renamed}
    let parents := info.parentInfo.map fun p =>
      {p with structName := renamed p.structName, projFn := renamed p.projFn}
    env := structureExt.addEntry env {info with structName := name, fieldInfo := fields, parentInfo := parents}
  for (name, info) in projectionFnInfoExt.getModuleEntries source idx (level := level) do
    if available.contains (renamed name) then
      let proj := renamed name
      env := projectionFnInfoExt.addEntry (asyncDecl := proj) env (proj, {info with ctorName := renamed info.ctorName})
  let mut entries := #[]
  for ext in ← persistentEnvExtensionsRef.get do
    if ext.name == structureExt.name || ext.name == projectionFnInfoExt.name then
      -- Structure registrations live in the main environment. Read the extension
      -- using its own mode so its local state survives distribution.
      let data := (ext.exportEntriesFn env (ext.getState env)).get level
      unless data.isEmpty do entries := entries.push (ext.name, data)
  return entries

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
  let defaults := Meta.defaultInstanceExtension
  for entry in defaults.getModuleEntries source idx (level := level) do
    if available.contains (renamed entry.instanceName) then
      env := defaults.addEntry env {entry with
        className := renamed entry.className, instanceName := renamed entry.instanceName}
  -- The two source registries already supplied only entries visible at this level.
  -- The scratch environment contains no declarations for a second visibility filter.
  return (← mkModuleData env .private).entries.filter fun e => e.1 == ext.ext.name || e.1 == defaults.name

/-- Definitions with pointwise computation equations checked by the interface audit. -/
private def sealedImplementation (n : Name) : Bool :=
  [`Fin.natAdd, `Option.isNone, `Array.modifyMUnsafe, `Lean.Grind.CommRing.Expr.denoteSAsRing,
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

unsafe def main (args : List String) : IO Unit := do
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
  let tokens := OmegaChecks.InitPort.LogicalHandle.apis.map (fun api => (api.tokenName, api.owner))
  let loopHelpers := OmegaChecks.InitPort.LawfulLoop.rules.map fun rule => (rule.helper, rule.owner)
  let matchHelpers := OmegaChecks.InitPort.PatternMatch.rules.map (fun rule => (rule.helper, rule.owner))
  let exposedHelpers := loopHelpers ++ matchHelpers
  let localHelpers := exposedHelpers ++ tokens ++ OmegaChecks.InitPort.ReferenceSpecialization.supportOwners
  let mut groups : NameMap (Array (Name × ConstantInfo)) := {}
  let mut generatedOwners : NameMap Name := {}
  for ci in newDecls.constants do
    let (upstream, owner) ← if let some entry := localHelpers.find? (fun (n, _) => ci.name == renamed n) then
      pure entry
    else do
      let some upstream := reverseNames[ci.name]? | throw <| IO.userError s!"no official name for {ci.name}"
      pure (upstream, (officialModuleName source upstream).get!)
    generatedOwners := generatedOwners.insert ci.name (owner.replacePrefix `Init `OmegaInit)
    groups := groups.insert owner ((groups.getD owner #[]).push (upstream,ci))
  -- A localized proof can mention a private helper from the strict seed that has no
  -- official name. Use its physical owner when building each module's dependency graph.
  let dependencyOwner := fun (name : Name) => generatedOwners.find? name <|> do
    let i ← monolith.getModuleIdxFor? name
    let home := monolith.header.moduleNames[i]!
    guard (home.getRoot == `OmegaInit)
    return home
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
    -- Compiled syntax rendering and line readers use these private imports in their executable bodies.
    let retained := source.header.moduleData[idx]!.imports.filter fun i =>
      i.isExported || (official == `Init.Data.Format.Syntax && i.module == `Init.Data.ToString.Name) ||
        (official == `Init.System.IO && i.module == `Init.Data.String.TakeDrop)
    let mut mappedImports := retained.map fun i =>
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
      let later := fun n => (dependencyOwner n >>= order.find?).any (· > rank)
      group ← group.mapM fun (n, ci) => return (n, ← localizeProof monolith later ci)
    kept := kept + group.size
    if !group.isEmpty then keptOwners := keptOwners + 1
    for (originalName, ci) in group do
      let mut edges := #[]
      let deps := (declarationDependencies ci).toArray
      for dep in deps do
        if let some target := dependencyOwner dep then
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
    let nameCode ← if owner == `OmegaInit.Dynamic && ([`TypeName.mk, OmegaChecks.InitPort.TypeName.reader].any sourceNames.contains) then
      some <$> OmegaChecks.InitPort.TypeName.nativeEntries source monolith owner renamed sourceNames.contains
      else pure none
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
        if i == 2 || exposedHelpers.any (·.1 == n) then cs := cs.push new
        else if let some exposed := publiclyDeclared.find? n then
          if (exposed.isAxiom || sealedImplementation n) && !new.isAxiom then
            let hidden := ConstantInfo.axiomInfo {new.toConstantVal with isUnsafe := new.isUnsafe}
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
      let structures ← structureEntries source monolith idx owner available level
      let tags ← elaboratorEntries source surface monolith idx owner available level
      let entries := (previous.entries.filter (fun e =>
        !selected.contains e.1 && e.1 != Meta.instanceExtension.ext.name && e.1 != Meta.defaultInstanceExtension.name &&
        e.1 != structureExt.name && e.1 != projectionFnInfoExt.name &&
        e.1 != matchPatternAttr.ext.name && e.1 != Elab.Term.elabAsElim.ext.name &&
        e.1 != Meta.coeDeclAttr.ext.name && e.1 != neverExtractAttr.ext.name && e.1 != auxRecExt.name && e.1 != aliasExtension.name &&
        e.1 != Meta.Match.Extension.extension.name)) ++ replacement ++ instances ++ structures ++ tags
      let mut entries := entries
      if let some compiled := nameCode then
        let generated ← OmegaChecks.InitPort.TypeName.publicCompilerEntries compiled
        for (key, extra) in generated do
          let old := ((entries.find? (·.1 == key)).map Prod.snd).getD #[]
          let name (v : EnvExtensionEntry) := (unsafeCast v : Name × Unit).1
          let merged := old.foldl (init := extra) fun a v => if a.any (fun e => name e == name v) then a else a.push v
          entries := (entries.filter (·.1 != key)).push (key, merged.qsort (fun a b => (name a).quickLt (name b)))
      let hidden := tokens.filter fun (n, o) => i == 2 && o == official && cs.any (·.name == renamed n)
      unless hidden.isEmpty do
        let tags := hidden.foldl (init := (← mkEmptyEnvironment).setMainModule owner)
          (fun env (n, _) => addNoncomputable env (renamed n))
        let tagged ← mkModuleData tags .private
        entries := entries ++ tagged.entries.filter (fun e => e.1 == noncomputableExt.name && !e.2.isEmpty)
      let extraConstNames := if nameCode.isSome then
          (exported.extraConstNames.filter sourceNames.contains |>.map renamed).foldl
            (fun acc name => if acc.contains name then acc else acc.push name) previous.extraConstNames
        else previous.extraConstNames
      let data : ModuleData := { previous with entries, extraConstNames, isModule := true, imports := mergeImports previous.imports mappedImports, constants := cs, constNames := cs.map (·.name) }
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
    if let some compiled := nameCode then
      OmegaChecks.InitPort.NativeState.writeCode out owner compiled OmegaChecks.InitPort.NativeState.codeExtensions
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
      let dependencies := (toJson imports).compress
      edgeInfo.putStrLn (toJson #[dep, "", dependencies, dependencies]).compress
      pending := pending ++ imports
      for ext in #["olean", "olean.server", "olean.private", "ir", "ir.sig"] do
        let to := modToFilePath out name ext
        IO.FS.createDirAll to.parent.get!
        IO.FS.writeBinFile to (← IO.FS.readBinFile (modToFilePath seed name ext))
      copied := copied.insert name
  IO.FS.writeFile (out.parent.get! / "modules.json") (toJson graph).compress
  IO.println s!"Wrote {count} modules and {kept} additions in {keptOwners} owners."
