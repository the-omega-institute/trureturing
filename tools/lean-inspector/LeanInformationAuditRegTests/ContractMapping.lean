import LeanInformationAudit.ContractPrototype.Equivalence

namespace LeanInformationAuditRegTests.ContractMapping
open Lean Meta LeanInformationAudit
open ContractPrototype.Equivalence
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

def alternativeCut := @cutRealization

private def rejected (label expected : String) (action : MetaM Json) : MetaM Json := do
  let error ← tryCatchRuntimeEx (do discard action; pure none)
    (fun error => pure (some error))
  let some error := error | do
    logError m!"[FAIL] comparator_rejects_{label}"
    return Json.mkObj [("test", toJson label), ("rejected", toJson false)]
  let diagnostic ← error.toMessageData.toString
  unless diagnostic.contains expected do
    logError m!"[FAIL] comparator_wrong_rejection:{label}:{diagnostic}"
  logInfo m!"[PASS] comparator_rejects_{label}: {diagnostic}"
  return Json.mkObj [("test", toJson label), ("rejected", toJson true),
    ("diagnostic", toJson diagnostic)]

/-- Same-type semantic changes are tested independently of owner authorization. -/
def run (oldEnv newEnv : Environment) (mapping : NameMapping)
    (oldRecord newRecord : BindingRecord) : MetaM (Array Json) := do
  let .declaredValidated certificate := newRecord.result | throwError "mapping_control_not_validated"
  discard <| verifyRecord oldEnv newEnv mapping oldRecord newRecord
  let changed ← inEnvironment newEnv <| mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization #[mkConst ``Bool.not]
  let some original := newRecord.descriptor | throwError "mapping_control_descriptor_missing"
  inEnvironment newEnv do
    unless ← isDefEq (← inferType original) (← inferType changed) do
      throwError "readout_mutation_type_changed"
  let .ok (identity, _) ← inEnvironment newEnv <| TemplateAudit.rawIdentity
      newRecord.occurrence.levelParams changed
    | throwError "mutation_fingerprint_failed"
  let readout ← rejected "same_type_readout" "descriptor.mapped" <|
    verifyRecord oldEnv newEnv mapping oldRecord { newRecord with
      descriptor := some changed
      result := .declaredValidated { certificate with descriptorIdentity := identity } }
  let info ← inEnvironment newEnv <| getConstInfo newRecord.occurrence.realizationName
  let actual := info.type.getAppArgs[2]!
  inEnvironment newEnv do
    unless ← isDefEq (← inferType actual) (← inferType changed) do
      throwError "primitive_mutation_type_changed"
  let primitive ← rejected "same_type_primitive" "actual.mapped" <|
    verifyRecord oldEnv newEnv mapping oldRecord { newRecord with
      result := .declaredValidated { certificate with actualIdentity := identity } }
  let alternate := mkAppN (mkConst ``alternativeCut original.getAppFn.constLevels!) original.getAppArgs
  inEnvironment newEnv do
    unless ← isDefEq (← inferType original) (← inferType alternate) do
      throwError "template_mutation_type_changed"
  let template ← rejected "same_type_template_selection" "unregistered_template" <|
    verifyRecord oldEnv newEnv mapping oldRecord { newRecord with descriptor := some alternate }
  let owner ← rejected "unauthorized_owner" "unit_algorithm" <|
    verifyRecord oldEnv newEnv mapping oldRecord { newRecord with
      occurrence := { newRecord.occurrence with
        unitName := `Reg.ContractPrototype.Other.unit
        key := { newRecord.occurrence.key with registrationModule := `Reg.ContractPrototype.Other } } }
  let collision ← rejected "mapping_collision" "owner_collision" do
    validatePrefixes #[(mapping[0]!.1, mapping[0]!.2), (`Reg.Unrelated, mapping[0]!.2)]
    return Json.null
  let injection ← rejected "generated_name_collision" "name_collision" do
    validateInjection #[(`Reg.A.x, `Reg.B.x), (`Reg.A.y, `Reg.B.x)]
    return Json.null
  let text := toJson mapping[0]!.1.toString
  let payload := Json.mkObj [("source_name", text), ("label", text),
    ("readouts", Json.arr #[Json.mkObj [("path", Json.arr #[text])]])]
  let mapped := renameSourceBinding mapping payload
  unless (mapped.getObjVal? "label").toOption == (payload.getObjVal? "label").toOption &&
      (mapped.getObjVal? "readouts").toOption == (payload.getObjVal? "readouts").toOption &&
      (mapped.getObjVal? "source_name").toOption == some (toJson mapping[0]!.2.toString) do
    throwError "comparator_rewrites_nonidentity_json_field"
  return #[readout, primitive, template, owner, collision, injection,
    Json.mkObj [("test", toJson "json_field_roles"), ("verified", toJson true)]]

end LeanInformationAuditRegTests.ContractMapping
