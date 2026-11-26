import Lean
import Lean.Elab.ParseImportsFast

open Lean

namespace OmegaChecks.ModuleSurface

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
   aliasExtension.name, classExtension.name, Meta.instanceExtension.ext.name, Meta.simpExtension.ext.name, auxRecExt.name,
   protectedExt.name, matchPatternAttr.ext.name, Elab.Term.elabAsElim.ext.name, reducibilityCoreExt.name,
   -- Module provenance, compiled representation and kernel bookkeeping in the pinned toolchain.
   `Lean.namespacesExt, `Lean.noncomputableExt, `Lean.Compiler.inlineAttrs, `Lean.exportedAxiomsExt,
   `Lean.privateConstKindsExt, `Lean.modPkgExt, `Lean.IR.declMapExt, `Lean.Compiler.LCNF.baseExt,
   `Lean.Compiler.LCNF.monoExt, `Lean.Compiler.LCNF.impureSigExt, `Lean.Compiler.LCNF.trivialStructureInfoExt,
   `Lean.Compiler.LCNF.monoTypeExt, `Lean.Compiler.LCNF.impureTypeExt,
   `Lean.Compiler.LCNF.impureTrivialStructureInfoExt, `Lean.Compiler.LCNF.ctorLayoutExt,
   `Lean.indirectModUseExt, `Lean.deprecatedModuleExt].contains (privateToUserName name)

private def checkElaboration (env : Environment) (owner : Name) (idx : ModuleIdx) : IO Unit := do
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
def check (strict : Environment) : IO (Array (Name × Name)) := do
  let mut roots : NameMap Name := {}
  for port in strict.allImportedModuleNames do
    if !isBasis port then continue
    let some idx := strict.getModuleIdx? port | throw <| IO.userError s!"missing module {port}"
    checkElaboration strict port idx
    if port == port.getRoot then
      unless (Meta.instanceExtension.ext.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched instance registration in the {port} umbrella"
      unless (Meta.simpExtension.ext.getModuleEntries strict idx).isEmpty do
        throw <| IO.userError s!"unmatched simp registration in the {port} umbrella"
      checkUmbrella strict port idx
      continue
    let official := counterpart port
    let reference ← importModules #[{module := official}] {} (level := .exported)
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
        roots := roots.insert name expected
      for (alias, target) in aliasExtension.getModuleEntries strict idx do
        let officialAlias := alias.replacePrefix `Omega .anonymous
        let officialTarget := target.replacePrefix `Omega .anonymous
        let resolved := ResolveName.resolveGlobalName reference {} .anonymous [] officialAlias
        unless resolved == [(officialTarget, [])] do
          throw <| IO.userError s!"unmatched public alias {alias} for {target} exposed by {port} in {official}"
        let some home := strict.getModuleIdxFor? target | throw <| IO.userError s!"unknown alias target {target}"
        roots := roots.insert target (counterpart strict.header.moduleNames[home]!)
  return roots.toList.toArray

end OmegaChecks.ModuleSurface
