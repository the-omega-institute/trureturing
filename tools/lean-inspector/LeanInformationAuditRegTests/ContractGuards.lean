import LeanInformationAuditRegTests.ContractAssertions
import LeanInformationAudit.Contract.Decoder
import LeanInformationAudit.Contract.SourceAudit
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

def delayedSeal (_ : Unit) : LeanInformationAudit.Contract.Seal.{0,0} := structureForm

run_meta do
  let delayed ← getConstInfo ``delayedSeal
  assertTest "discovery.function_returning_contract_is_input"
    (LeanInformationAudit.Contract.SourceAudit.isInput delayed)
  assertTest "discovery.function_returning_contract_cannot_decode"
    (match LeanInformationAudit.Contract.SourceAudit.checkInputDefinition delayed with
      | .error reason => reason == s!"contract.cannot_decode:{delayed.name}:computed_type"
      | .ok _ => false)
  for name in #[``LeanInformationAudit.Contract.Seal.mk,
      ``LeanInformationAudit.Contract.Seal.rec] do
    assertTest "discovery.compiler_schema_declaration_is_not_input"
      (!LeanInformationAudit.Contract.SourceAudit.isInput (← getConstInfo name))

run_meta do
  for name in #[``structureForm, ``constructorForm, ``referenceForm, ``updatedForm] do
    let .defnInfo info ← getConstInfo name | throwError "compiled form definition missing"
    let decoded ← LeanInformationAudit.Contract.Decoder.liftLiteral <|
      LeanInformationAudit.Contract.Decoder.readSeal ((← getEnv).find? ·)
        (← collectAxioms name) name info.value
    assertTest s!"compiled_forms.{name.getString!}"
      (decoded.rootId == `CompiledContractForms && decoded.catalogs.isEmpty)


run_meta do
  let env := (← getEnv).setExporting false
  let interfaceModules := env.header.moduleNames.filter
    ((`LeanInformationAuditInterface.Contract).isPrefixOf ·)
  assertTest "interface.contract_modules" (interfaceModules.size >= 4)
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
