module
public import Lean
public import OmegaChecks.InitPort.TaskNames
import Lean.Elab.ParseImportsFast
import Lean.Compiler.LCNF.SpecInfo
import all Lean.Structure

public section

open Lean

namespace OmegaChecks.ModuleSurface

/-- Restore name resolution from the alias entries of an isolated compiled environment. -/
def withImportedAliases (env : Environment) : Environment := Id.run do
  let mut aliases : AliasState := {}
  for idx in [:env.header.modules.size] do
    aliases := (aliasExtension.getModuleEntries env idx).foldl addAliasEntry aliases
  return aliasExtension.setState env aliases.switch

def isBasis (owner : Name) : Bool :=
  owner.getRoot == `OmegaInit || owner.getRoot == `OmegaMathlib

private def counterpart (owner : Name) : Name :=
  owner.replacePrefix owner.getRoot (if owner.getRoot == `OmegaInit then `Init else `Mathlib)

/-- Include modules independently of the presence of local mathematical declarations. -/
def officialModules (strict : Environment) (lib : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for owner in strict.allImportedModuleNames do
    if !isBasis owner || owner == `OmegaMathlib then continue
    let official := counterpart owner
    let file := if owner.getRoot == `OmegaInit then modToFilePath lib official "olean"
      else modToFilePath ".lake/packages/mathlib" official "lean"
    unless ← file.pathExists do
      throw <| IO.userError s!"no official module {official} for {owner}"
    modules := modules.push official
  return modules

/-- The modules exposed when a consumer imports this root alone. -/
def publicClosure (env : Environment) (root : Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  while let some owner := pending.back? do
    pending := pending.pop
    unless seen.contains owner do
      seen := seen.insert owner
      let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing module {owner}"
      for dep in env.header.moduleData[idx]!.imports do
        if dep.isExported then pending := pending.push dep.module
  return seen

/-- Read the Mathlib import index without requiring a full Mathlib build. Init's
compiled umbrella is shipped with Lean and its public imports can be followed directly. -/
private def checkUmbrella (env : Environment) (port : Name) (idx : ModuleIdx) : IO Unit := do
  let exports ← if port == `OmegaMathlib then do
    let path := ".lake/packages/mathlib/Mathlib.lean"
    let header ← Lean.parseImports' (← IO.FS.readFile path) path
    pure <| NameSet.ofList ((header.imports.filter (·.isExported)).map (·.module)).toList
  else do
    let reference ← importModules #[{module := `Init}] {} (level := .exported)
    publicClosure reference `Init
  let data := env.header.moduleData[idx]!
  unless data.constNames.isEmpty do
    throw <| IO.userError s!"the {port} umbrella must contain only public imports of checked ports"
  for dep in data.imports do
    unless dep.isExported && !dep.importAll && dep.module.getRoot == port && exports.contains (counterpart dep.module) do
      throw <| IO.userError s!"unmatched {port} umbrella import {dep.module}"
  unless (aliasExtension.getModuleEntries env idx).isEmpty do
    throw <| IO.userError s!"unmatched export alias in the {port} umbrella"
  unless (classExtension.getModuleEntries env idx).isEmpty do
    throw <| IO.userError s!"unmatched class registration in the {port} umbrella"

/-- The opaque .olean payload can be decoded only by its registered extension. Unknown
extension kinds therefore require a correspondence before a port can expose them. -/
private def supportedExtension (name : Name) : Bool :=
  [-- Compiled interface registrations checked by the port and kernel-interface audits.
   externAttr.ext.name, aliasExtension.name, classExtension.name, Meta.instanceExtension.ext.name, Meta.simpExtension.ext.name, auxRecExt.name,
   protectedExt.name, matchPatternAttr.ext.name, Elab.Term.elabAsElim.ext.name, reducibilityCoreExt.name,
   privateToUserName structureExt.name, projectionFnInfoExt.name,
   -- Module provenance, compiled representation and kernel bookkeeping in the pinned toolchain.
   `Lean.namespacesExt, `Lean.noncomputableExt, `Lean.Compiler.inlineAttrs, `Lean.exportedAxiomsExt,
   `Lean.privateConstKindsExt, `Lean.modPkgExt, `Lean.IR.declMapExt, `Lean.Compiler.LCNF.baseExt,
   `Lean.Compiler.LCNF.monoExt, `Lean.Compiler.LCNF.impureSigExt, `Lean.Compiler.LCNF.trivialStructureInfoExt,
   Compiler.LCNF.specExtension.name, Compiler.implementedByAttr.ext.name,
   `Lean.Compiler.LCNF.monoTypeExt, `Lean.Compiler.LCNF.impureTypeExt,
   `Lean.Compiler.LCNF.impureTrivialStructureInfoExt, `Lean.Compiler.LCNF.ctorLayoutExt,
   `Lean.indirectModUseExt, `Lean.deprecatedModuleExt].contains (privateToUserName name)

/-- The compiler may specialize a private helper inside a publicly callable definition. -/
private def checkSpecializations (env : Environment) (owner : Name) : IO Unit := do
  let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing native owner {owner}"
  let specs := Compiler.LCNF.specExtension.getModuleEntries env idx (level := .private)
  unless specs.isEmpty do
    let base := Compiler.LCNF.baseExt.getModuleEntries env idx (level := .private)
    for entry in specs do
      let some decl := base.find? (·.name == entry.declName)
        | throw <| IO.userError s!"no compiled signature for specialization of {entry.declName} in {owner}"
      unless env.getModuleIdxFor? entry.declName == some idx &&
          entry.paramsInfo.size == decl.params.size &&
          entry.paramsInfo.any Compiler.LCNF.SpecParamInfo.causesSpecialization do
        throw <| IO.userError s!"invalid parameter specialization for {entry.declName} in {owner}"

private def checkElaboration (env : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  for (n, data) in externAttr.ext.getModuleEntries env idx do
    let (expectedOwner, symbol) ← match n with
      | `Omega.ST.Prim.mkRef => pure (`OmegaInit.System.ST, "omega_st_mk_ref")
      | `Task.pure => pure (`OmegaInit.Core, "lean_task_pure")
      | `Task.get => pure (`OmegaInit.Core, "lean_task_get_own")
      | `Omega.IO.Promise.result? => pure (`OmegaInit.System.Promise, "lean_io_promise_result_opt")
      | `Omega.IO.Promise.new => pure (`OmegaInit.System.Promise, "omega_io_promise_new")
      | `Omega.IO.Promise.resolve => pure (`OmegaInit.System.Promise, "omega_io_promise_resolve")
      | `Omega.IO.Promise.isResolved => pure (`OmegaInit.System.Promise, "omega_io_promise_is_resolved")
      | _ => throw <| IO.userError s!"unverified native symbol for {owner}/{n}"
    unless owner == expectedOwner && env.getModuleIdxFor? n == some idx &&
        data == ⟨[.standard `all symbol]⟩ do throw <| IO.userError s!"invalid native state entry {owner}/{n}"
  for (n, implementation) in Compiler.implementedByAttr.ext.getModuleEntries env idx do
    let reader := mkPrivateNameCore `OmegaInit.Dynamic `Omega.TypeName.typeNameImpl
    unless owner == `OmegaInit.Dynamic && n == `Omega.TypeName.typeName && implementation == reader &&
        env.getModuleIdxFor? n == some idx && env.getModuleIdxFor? reader == some idx do
      throw <| IO.userError s!"unmatched native implementation {n} → {implementation} in {owner}"
  for entry in reducibilityExtraExt.ext.getModuleEntries env idx do
    let (name, _) := match entry with
      | .global value | .scoped _ value => value
    throw <| IO.userError s!"unverified public reducibility override for {name} in {owner}"
  let extensions := #[
    ("parser", (Parser.parserExtension.ext.getModuleEntries env idx).size),
    ("macro", (Elab.macroAttribute.ext.ext.getModuleEntries env idx).size),
    ("term elaborator", (Elab.Term.termElabAttribute.ext.ext.getModuleEntries env idx).size)]
  for (kind, count) in extensions do
    if count != 0 then
      throw <| IO.userError s!"no elaboration correspondence for public {kind} entries in {owner}"
  for (ext, entries) in env.header.moduleData[idx]!.entries do
    unless entries.isEmpty || supportedExtension ext do
      throw <| IO.userError s!"no elaboration correspondence for public environment extension {ext} in {owner}"

/-- Validate the metadata that ordinary field notation and structure literals consume. -/
private def checkStructures (port ref : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  let rename := fun (n : Name) => Id.run do
    if let some lexical := privatePrefix? n then
      if (`_private.OmegaInit).isPrefixOf lexical then
        return lexical.replacePrefix `_private.OmegaInit `_private.Init ++
          (privateToUserName n).replacePrefix `Omega .anonymous
    return n.replacePrefix `Omega .anonymous
  for s in structureExt.getModuleEntries port idx do
    let some (.inductInfo ind) := port.find? s.structName
      | throw <| IO.userError s!"registered structure {s.structName} is not an inductive type in {owner}"
    unless ind.ctors.length == 1 do
      throw <| IO.userError s!"registered structure {s.structName} must have one constructor in {owner}"
    let some target := getStructureInfo? ref (rename s.structName)
      | throw <| IO.userError s!"unknown public structure {s.structName} in {owner}"
    unless port.getModuleIdxFor? s.structName == some idx &&
        ref.getModuleIdxFor? target.structName == ref.getModuleIdx? (counterpart owner) &&
        s.fieldNames == target.fieldNames && s.fieldInfo.size == target.fieldInfo.size &&
        s.parentInfo.size == target.parentInfo.size do
      throw <| IO.userError s!"structure field order or owner mismatch for {s.structName}"
    for (f, g) in s.fieldInfo.zip target.fieldInfo do
      unless f.fieldName == g.fieldName && rename f.projFn == g.projFn &&
          f.subobject?.map rename == g.subobject? && f.binderInfo == g.binderInfo &&
          f.autoParam?.isNone && g.autoParam?.isNone do
        throw <| IO.userError s!"structure field mismatch for {s.structName}.{f.fieldName}"
    for (p, q) in s.parentInfo.zip target.parentInfo do
      unless rename p.structName == q.structName && p.subobject == q.subobject && rename p.projFn == q.projFn do
        throw <| IO.userError s!"structure parent mismatch for {s.structName}.{p.projFn}"
  for (name, info) in projectionFnInfoExt.getModuleEntries port idx do
    let some (.ctorInfo ctor) := port.find? info.ctorName
      | throw <| IO.userError s!"projection {name} has no constructor {info.ctorName} in {owner}"
    let some target := ref.getProjectionFnInfo? (rename name)
      | throw <| IO.userError s!"unmatched projection {name} in {owner}"
    unless port.getModuleIdxFor? name == some idx &&
        ref.getModuleIdxFor? (rename name) == ref.getModuleIdx? (counterpart owner) &&
        info.i < ctor.numFields && info.numParams == ctor.numParams && rename info.ctorName == target.ctorName &&
        info.numParams == target.numParams && info.i == target.i && info.fromClass == target.fromClass do
      throw <| IO.userError s!"projection metadata mismatch for {name} in {owner}"

private abbrev ClassParameters := Array Nat × Array Nat

private def checkInstances (env reference : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  let installed := Meta.instanceExtension.ext.getModuleEntries env idx
  if installed.isEmpty then return
  let rename := fun (n : Name) => n.replacePrefix `Omega .anonymous
  let key := fun (k : Meta.DiscrTree.Key) => match k with
    | .const n a => .const (rename n) a
    | .proj n i a => .proj (rename n) i a
    | k => k
  let load := fun (e : ScopedEnvExtension.Entry Meta.InstanceEntry) => match e with
    | .global v => (none, v)
    | .scoped ns v => (some ns, v)
  let some upstream := reference.getModuleIdx? (counterpart owner)
    | throw <| IO.userError s!"missing official owner for instances in {owner}"
  let actual := (Meta.instanceExtension.ext.getModuleEntries reference upstream).map load
  let mut last := 0
  for e in installed do
    let (scope, v) := load e
    let some name := v.globalName? | throw <| IO.userError s!"unnamed public instance in {owner}"
    let .const n us := v.val | throw <| IO.userError s!"invalid public instance term in {owner}"
    unless name == n && name.getRoot == `Omega && env.contains name && reference.contains (rename name) do
      throw <| IO.userError s!"no elaboration correspondence for public instance {name} in {owner}"
    -- Preserve the relative order of registered candidates, including priority ties.
    let mut found := false
    while last < actual.size && !found do
      let (targetScope, target) := actual[last]!
      last := last + 1
      found := targetScope == scope.map rename && target.globalName? == some (rename name) &&
        target.val.equal (.const (rename name) us) && target.priority == v.priority &&
        target.keys == v.keys.map key && target.synthOrder == v.synthOrder && target.attrKind == v.attrKind
    unless found do throw <| IO.userError s!"unmatched public instance registration for {name} in {owner}"

private def classParameters (env : Environment) (modules : Array ModuleIdx) : NameMap ClassParameters :=
  modules.foldl (init := {}) fun classes idx =>
    (classExtension.getModuleEntries env idx).foldl (init := classes) fun m entry =>
      m.insert entry.name (entry.outParams, entry.outLevelParams)

private def checkClasses (strict reference : Environment) (owner : Name) (idx : ModuleIdx)
    (strictClasses officialClasses : NameMap ClassParameters) : IO Unit := do
  -- Registrations can target an imported declaration, including a universe-output override.
  let registered := (classExtension.getModuleEntries strict idx).map (·.name)
  for name in registered ++ strict.header.moduleData[idx]!.constNames do
    if isPrivateName name || name.isInternal then continue
    let upstream := name.replacePrefix `Omega .anonymous
    if (registered.contains name && !reference.contains upstream) ||
        strictClasses.get? name != officialClasses.get? upstream then
      throw <| IO.userError s!"public class registration mismatch for {name} in {owner}"

private def checkSimp (strict reference : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
  for entry in Meta.simpExtension.ext.getModuleEntries strict idx do
    -- Unfolding a public definition needs the same upstream instruction and the
    -- definition-level body check. The public rule must not reveal a sealed implementation.
    let .global (.toUnfold name) := entry
      | throw <| IO.userError s!"no correspondence for public simp rewrite or scoped entry in {owner}"
    let upstream := name.replacePrefix `Omega .anonymous
    let isExposed := (strict.find? name).any (· matches .defnInfo _)
    let equivalent := reference.allImportedModuleNames.any fun moduleName => Id.run do
      let some i := reference.getModuleIdx? moduleName | return false
      return (Meta.simpExtension.ext.getModuleEntries reference i).any fun
        | .global (.toUnfold n) => n == upstream
        | _ => false
    unless isExposed && equivalent do
      throw <| IO.userError s!"unmatched public simp unfolding for {name} in {owner}"

/-- Check a port as seen by a consumer importing it alone. Re-exported foundation
declarations and alias targets are mathematical roots, even in a declaration-free module. -/
def check (strict : Environment) (full? : Option Environment := none) : IO (Array (Name × Name)) := do
  let strict := withImportedAliases strict
  let mut roots : NameMap Name := {}
  for port in strict.allImportedModuleNames do
    if !isBasis port then continue
    let some idx := strict.getModuleIdx? port | throw <| IO.userError s!"missing module {port}"
    checkElaboration strict port idx
    checkSpecializations (full?.getD strict) port
    if port == port.getRoot then
      unless (structureExt.getModuleEntries strict idx).isEmpty &&
          (projectionFnInfoExt.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched structure registration in the {port} umbrella"
      unless (Meta.instanceExtension.ext.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched instance registration in the {port} umbrella"
      unless (Meta.simpExtension.ext.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched simp registration in the {port} umbrella"
      checkUmbrella strict port idx
      continue
    let official := counterpart port
    let reference := withImportedAliases (← importModules #[{module := official}] {} (level := .exported))
    let officialClasses := classParameters reference (Array.range reference.header.modules.size)
    let visible ← publicClosure strict port
    let visibleIndices := (Array.range strict.header.modules.size).filter fun i =>
      visible.contains strict.header.moduleNames[i]!
    let strictClasses := classParameters strict visibleIndices
    -- Diagnose the port's own public registrations before those of a re-export.
    for owner in port :: (visible.erase port).toList do
      let some idx := strict.getModuleIdx? owner | throw <| IO.userError s!"missing module {owner}"
      if owner != port then checkElaboration strict owner idx
      let data := strict.header.moduleData[idx]!
      checkStructures strict reference owner idx
      checkInstances strict reference owner idx
      checkClasses strict reference owner idx strictClasses officialClasses
      checkSimp strict reference owner idx
      if data.imports.any (fun dep => dep.isExported && dep.importAll) then
        throw <| IO.userError s!"unverified public import all exposed by {owner}"
      for name in data.constNames do
        if isPrivateName name || name.isInternal then continue
        let expected := counterpart owner
        let translated := name.replacePrefix `Omega .anonymous
        unless reference.contains translated do
          throw <| IO.userError s!"{official} does not publicly expose {translated} for {name} in {port}"
        unless isProtected strict name == isProtected reference translated do
          throw <| IO.userError s!"protected modifier mismatch for {name} in {official}"
        if hasMatchPatternAttribute strict name && !hasMatchPatternAttribute reference translated then
          throw <| IO.userError s!"unmatched match_pattern attribute for {name} in {official}"
        if Elab.Term.elabAsElim.hasTag strict name && !Elab.Term.elabAsElim.hasTag reference translated then
          throw <| IO.userError s!"unmatched elab_as_elim attribute for {name} in {official}"
        if let some (alias, target) := OmegaChecks.InitPort.TaskNames.aliasFor? translated then
          unless name == target && (aliasExtension.getModuleEntries strict idx).contains (alias, target) &&
              ResolveName.resolveGlobalName strict {} .anonymous [] alias == [(target, [])] do
            throw <| IO.userError s!"missing or ambiguous task alias {alias} for {target} in {owner}"
        roots := roots.insert name expected
      for (alias, target) in aliasExtension.getModuleEntries strict idx do
        let officialAlias := alias.replacePrefix `Omega .anonymous
        let officialTarget := target.replacePrefix `Omega .anonymous
        let resolved := ResolveName.resolveGlobalName reference {} .anonymous [] officialAlias
        let some originalOwner := reference.getModuleIdx? (counterpart owner)
          | throw <| IO.userError s!"missing owner of alias {alias} in {official}"
        let taskAlias := OmegaChecks.InitPort.TaskNames.aliasFor? officialTarget == some (alias, target) &&
          strict.getModuleIdxFor? target == some idx && reference.getModuleIdxFor? officialTarget == some originalOwner
        unless (taskAlias || (aliasExtension.getModuleEntries reference originalOwner).contains (officialAlias, officialTarget)) &&
            resolved == [(officialTarget, [])] do
          throw <| IO.userError s!"unmatched public alias {alias} for {target} exposed by {port} in {official}"
        let some home := strict.getModuleIdxFor? target | throw <| IO.userError s!"unknown alias target {target}"
        roots := roots.insert target (counterpart strict.header.moduleNames[home]!)
  return roots.toList.toArray

end OmegaChecks.ModuleSurface
