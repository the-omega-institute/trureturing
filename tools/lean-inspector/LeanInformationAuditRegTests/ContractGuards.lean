import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAudit.Contract.Discovery
import LeanInformationAudit.Contract.InterfaceGuard
import D5.S3.ConceptDynamics.InformationEscape.Arena

namespace LeanInformationAuditRegTests.ContractGuards
open Lean Meta Elab Command

def finiteArena : D5.S3.ConceptDynamics.InformationEscape.Arena where
  State := Bool
  stateFintype := inferInstance
  stateDecidableEq := inferInstance

def metadataRoot : Lean.Name := `CompiledContractForms

def structureForm : LeanInformationAudit.Contract.Seal.{0,0} :=
  { rootId := metadataRoot, catalogs := #[], options := #[] }

def constructorForm : LeanInformationAudit.Contract.Seal.{0,0} :=
  ⟨metadataRoot, #[], #[]⟩

abbrev referenceForm : LeanInformationAudit.Contract.Seal.{0,0} := structureForm

def updatedForm : LeanInformationAudit.Contract.Seal.{0,0} :=
  { structureForm with rootId := metadataRoot, catalogs := #[], options := #[] }

run_meta do
  for name in #[``structureForm, ``constructorForm, ``referenceForm, ``updatedForm] do
    let .defnInfo info ← getConstInfo name | throwError "compiled form definition missing"
    let decoded ← LeanInformationAudit.Contract.Decoder.readSeal name info.value
    assertTest s!"compiled_forms.{name.getString!}"
      (decoded.rootId == `CompiledContractForms && decoded.catalogs.isEmpty)


run_meta do
  let env := (← getEnv).setExporting false
  let interfaceModules := env.header.moduleNames.filter
    ((`LeanInformationAuditInterface.Contract).isPrefixOf ·)
  assertTest "interface.contract_modules" (interfaceModules.size >= 4)
  for owner in interfaceModules do
    let result := LeanInformationAudit.Contract.InterfaceGuard.audit env owner
    assertTest s!"interface.types_only.{owner.getString!}" result.isOk
    if let .error error := result then logInfo m!"CONTRACT_DIAGNOSTIC {error}"
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
    ``LeanInformationAudit.Contract.BoundTheoremUnit,
    ``LeanInformationAudit.Contract.Implementation.PartialSlotEvidence,
    ``LeanInformationAudit.Contract.Implementation.Correspondence,
    ``LeanInformationAudit.Contract.Implementation.WitnessVariationEvidence,
    ``LeanInformationAudit.Contract.SealRow,
    ``LeanInformationAudit.Contract.SealCatalog,
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
    if (env.getModuleIdxFor? name).any (fun index =>
        interfaceModules.contains env.allImportedModuleNames[index.toNat]!) then
      pending := pending.push name
  let roots := pending.size
  let mut seen : NameSet := {}
  let mut forbidden : Array Name := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if #[`Lean.Meta.evalExpr, `Lean.evalConst, `Lean.evalConstCheck,
        `Lean.evalConstCheck', `Lean.Meta.evalExprCore, `Lean.Meta.whnf, `Lean.Meta.isDefEq].contains name then
      forbidden := forbidden.push name
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  assertTest "compiled_guard_native" forbidden.isEmpty
  logInfo m!"CONTRACT_NATIVE_DEPENDENCIES roots={roots} visited={seen.size} forbidden={forbidden}"

end LeanInformationAuditRegTests.ContractGuards
