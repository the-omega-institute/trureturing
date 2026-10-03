import LeanInformationAudit.ContractPrototype.NameMapping
import Lean.Compiler.CSimpAttr
import Lean.Compiler.InitAttr
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.ExportAttr
import Lean.Compiler.NeverExtractAttr
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.IR.UnboxResult

import LeanInformationAudit.ContractPrototype.CompilerAttributes

namespace LeanInformationAudit.ContractPrototype.Equivalence
open Lean Meta Compiler

/-- Compiler replacement edges and foreign implementation descriptions are
inspected as data. The equivalence judge never evaluates their targets. -/
structure ImplementationIdentity where
  targets : Array (String × Name) := #[]
  compilerPasses : Array Name := #[]
  externData : Option ExternAttrData := none
  flags : String := ""
  deriving Inhabited, BEq

structure ImplementationDependencyIdentity extends TemplateAudit.DependencyIdentity where
  implementation : ImplementationIdentity
  deriving Inhabited

/-- Custom repository compiler passes have unrestricted transformation power.
Only pinned upstream installers are accepted; their code is never invoked here. -/
def verifyCompilerPasses (env : Environment) : MetaM (Array Name) := do
  let extension := Compiler.LCNF.passManagerExt
  let mut installers := #[]
  for index in [:env.header.modules.size] do
    installers := installers ++ extension.getModuleEntries env index
  installers := installers ++ (extension.getState env).1.reverse.toArray
  for name in installers do
    let owner := (RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule
    if Repository.isModule owner then
      throwError "contract.equivalence:implementation_shape:cpass:{name}"
    unless env.contains name do
      throwError "contract.equivalence:implementation_target_missing:cpass:{name}"
  return installers

/-- Lean's pinned compiler substitutes implemented_by, unsafe recursive bodies,
csimp replacements and init/builtin_init values. Inline/specialization/export
attributes control compilation of the same body and are retained as metadata. -/
def implementationIdentity (env : Environment) (info : ConstantInfo) (owner : Name)
    (compilerPasses : Array Name := #[]) :
    MetaM ImplementationIdentity := do
  let mut targets := compilerPasses.map fun name => ("cpass", name)
  if let some target := Compiler.getImplementedBy? env info.name then
    targets := targets.push ("implemented_by", target)
  let recursive := Compiler.mkUnsafeRecName info.name
  if let some implementation := env.find? recursive then
    match implementation with
    | .defnInfo value =>
      unless value.safety == DefinitionSafety.unsafe || value.safety == DefinitionSafety.partial do
        throwError "contract.equivalence:implementation_shape:unsafe_rec:{info.name}"
    | _ => throwError "contract.equivalence:implementation_shape:unsafe_rec:{info.name}"
    targets := targets.push ("unsafe_rec", recursive)
  if let some entry := (Compiler.CSimp.ext.getState env).map.find? info.name then
    unless entry.fromDeclName == info.name do
      throwError "contract.equivalence:implementation_shape:csimp:{info.name}"
    targets := targets ++ #[("csimp", entry.toDeclName), ("csimp_proof", entry.thmName)]
  for (kind, initializationAttr) in #[("init", regularInitAttr), ("builtin_init", builtinInitAttr)] do
    if let some target := initializationAttr.getParam? env info.name then
      if target.isAnonymous then
        if Repository.isModule owner then
          throwError "contract.equivalence:implementation_shape:{kind}.anonymous:{info.name}"
      else targets := targets.push (kind, target)
  for (kind, target) in targets do
    unless env.contains target do
      throwError "contract.equivalence:implementation_target_missing:{kind}:{info.name}:{target}"
  let externData := getExternAttrData? env info.name
  if let some data := externData then
    if data.entries.isEmpty then
      throwError "contract.equivalence:implementation_shape:extern.empty:{info.name}"
    for entry in data.entries do
      unless #[`all, `c, `cpp, `llvm].contains entry.backend do
        throwError "contract.equivalence:implementation_shape:extern.backend:{info.name}:{entry.backend}"
      match entry with
      | .standard _ _ | .inline _ _ => pure ()
      | .adhoc _ | ExternEntry.opaque =>
        if Repository.isModule owner then
          throwError "contract.equivalence:implementation_shape:extern.unidentified:{info.name}"
  let inlineKind := (Compiler.getInlineAttribute? env info.name).map fun kind =>
    match kind with
    | .inline => "inline"
    | .noinline => "noinline"
    | .macroInline => "macro_inline"
    | .inlineIfReduce => "inline_if_reduce"
    | .alwaysInline => "always_inline"
  let definitionSafety := match info with
    | .defnInfo value => some <| match value.safety with
      | DefinitionSafety.safe => "safe"
      | DefinitionSafety.unsafe => "unsafe"
      | DefinitionSafety.partial => "partial"
    | _ => none
  let flags := (Json.mkObj [
    ("definition_safety", toJson definitionSafety),
    ("unsafe", toJson info.isUnsafe),
    ("meta", toJson (isMarkedMeta env info.name)),
    ("unbox", toJson (IR.UnboxResult.hasUnboxAttr env info.name)),
    ("tagged_return", toJson (CompilerAttributes.taggedReturnAttribute.hasTag env info.name)),
    ("noncomputable", toJson (isNoncomputable env info.name)),
    ("inline", toJson inlineKind),
    ("init", toJson ((regularInitAttr.getParam? env info.name).isSome)),
    ("builtin_init", toJson ((builtinInitAttr.getParam? env info.name).isSome)),
    ("csimp_lemma", toJson (Compiler.hasCSimpAttribute env info.name)),
    ("never_extract", toJson (hasNeverExtractAttribute env info.name)),
    ("specialize", toJson (hasSpecializeAttribute env info.name)),
    ("nospecialize", toJson (hasNospecializeAttribute env info.name)),
    ("weak_specialize", toJson (hasWeakSpecializeAttribute env info.name)),
    ("specialization_args", toJson (getSpecializationArgs? env info.name)),
    ("export", toJson ((getExportNameFor? env info.name).map Name.toString))]).compress
  return { targets, compilerPasses, externData, flags }

def renameImplementation (mapping : NameMapping) (value : ImplementationIdentity) :
    ImplementationIdentity :=
  { value with
    targets := value.targets.map fun (kind, name) => (kind, renameName mapping name)
    compilerPasses := value.compilerPasses.map (renameName mapping) }

end LeanInformationAudit.ContractPrototype.Equivalence
