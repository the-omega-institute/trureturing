import LeanInformationAudit.Contract.Discovery

namespace LeanInformationAuditRegTests.ContractGuards
open Lean Meta Elab Command

def assertTest (label : String) (ok : Bool) : MetaM Unit := do
  if ok then logInfo m!"[PASS] {label}"
  else logError m!"[FAIL] {label}"

run_meta do
  let env := (← getEnv).setExporting false
  let structures := #[
    ``LeanInformationAudit.Contract.Ref, ``LeanInformationAudit.Contract.OptionSetting,
    ``LeanInformationAudit.Contract.ReadoutSelection,
    ``LeanInformationAudit.Contract.DefinitionSelection,
    ``LeanInformationAudit.Contract.SourceSelection,
    ``LeanInformationAudit.Contract.Registration,
    ``LeanInformationAudit.Contract.TypeRef,
    ``LeanInformationAudit.Contract.TemplateEnrollment,
    ``LeanInformationAudit.Contract.ExpectedOccurrence,
    ``LeanInformationAudit.Contract.RootCatalogData,
    ``LeanInformationAudit.Contract.RootCatalog,
    ``LeanInformationAudit.Contract.ExpectedDeclaration,
    ``LeanInformationAudit.Contract.Seal]
  let mut fields : Nat := 0
  for structureName in structures do
    let names := getStructureFields env structureName
    assertTest s!"defaults.structure.{structureName}" (!names.isEmpty)
    for field in names do
      fields := fields + 1
      assertTest s!"defaults.field.{structureName}.{field}"
        ((getEffectiveDefaultFnForField? env structureName field).isNone)
  logInfo m!"CONTRACT_DEFAULT_FIELDS {fields}"
  let mut pending : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`LeanInformationAudit.Contract).isPrefixOf name then pending := pending.push name
  let roots := pending.size
  let mut seen : NameSet := {}
  let mut forbidden : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if #[`Lean.Meta.evalExpr, `Lean.evalConst, `Lean.evalConstCheck,
        `Lean.evalConstCheck', `Lean.Meta.evalExprCore].contains name then
      forbidden := forbidden.push name
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  assertTest "compiled_guard_native" forbidden.isEmpty
  logInfo m!"CONTRACT_NATIVE_DEPENDENCIES roots={roots} visited={seen.size} forbidden={forbidden}"

end LeanInformationAuditRegTests.ContractGuards
