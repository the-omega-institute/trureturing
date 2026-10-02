import LeanInformationAudit.ContractPrototype.Equivalence

def Reg.MappingFixture.Source.x : Nat := 0
def Reg.MappingFixture.Target.x : Nat := 1

namespace LeanInformationAuditRegTests.ContractMapping
open Lean Meta LeanInformationAudit
open ContractPrototype.Equivalence
open D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates

def inlineAuthorization (owners : NameMapping) : Authorization := {
  owners
  generatedBridges := #[
    (`Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion ++
      (`D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion.bounded_run_union_boundary).str
        primitiveRealizationSuffix,
      `Reg.ContractPrototype.Inline.bridge)] }

def alternativeCut := @cutRealization

def rejected (label expected : String) (action : MetaM Json) : MetaM Json := do
  let error ← tryCatchRuntimeEx (do discard <| withCurrHeartbeats action; pure none)
    (fun error => pure (some error))
  let some error := error | do
    logError m!"[FAIL] comparator_rejects_{label}"
    return Json.mkObj [("test", toJson label), ("rejected", toJson false)]
  let diagnostic ← error.toMessageData.toString
  unless (expected.splitOn "|").any (fun text => diagnostic.contains text) do
    logError m!"[FAIL] comparator_wrong_rejection:{label}:{diagnostic}"
  logInfo m!"[PASS] comparator_rejects_{label}: {diagnostic}"
  return Json.mkObj [("test", toJson label), ("rejected", toJson true),
    ("diagnostic", toJson diagnostic)]

/-- Same-type semantic changes are tested independently of owner authorization. -/
def run (oldEnv newEnv : Environment) (mapping : NameMapping)
    (oldRecord newRecord : BindingRecord) : MetaM (Array Json) := do
  let .declaredValidated certificate := newRecord.result | throwError "mapping_control_not_validated"
  let output ← withCurrHeartbeats <| verifyRecord oldEnv newEnv (inlineAuthorization mapping) oldRecord newRecord
  let changed ← inEnvironment newEnv <| mkAppM
    `D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates.cutRealization #[mkConst ``Bool.not]
  let some original := newRecord.descriptor | throwError "mapping_control_descriptor_missing"
  inEnvironment newEnv do
    unless ← isDefEq (← inferType original) (← inferType changed) do
      throwError "readout_mutation_type_changed"
  let .ok (identity, _) ← inEnvironment newEnv <| TemplateAudit.rawIdentity
      newRecord.occurrence.levelParams changed
    | throwError "mutation_fingerprint_failed"
  let stale ← rejected "stale_target_descriptor" "new.current_descriptor|descriptor.new|unregistered_template" <|
    verifyRecord oldEnv newEnv (inlineAuthorization mapping) oldRecord
      { newRecord with descriptor := some changed }
  let rawClaims := TemplateBinding.ownedClaims newEnv
  let changedEnvironment := (TemplateBinding.ownedEvents newEnv).foldl
    (fun env (_, event) => TemplateBinding.addOccurrence env event)
    (TemplateBinding.resetAssessmentRecords newEnv)
  let changedEnvironment := rawClaims.foldl (fun env (_, claim) => TemplateBinding.addClaim env
    (if claim.key == newRecord.occurrence.key then { claim with descriptor := some changed }
      else claim)) changedEnvironment
  let environmentClaim ← rejected "stale_environment_claim" "new.current_descriptor|new.current_result" <|
    verifyRecord oldEnv changedEnvironment (inlineAuthorization mapping) oldRecord newRecord
  let readout ← rejected "same_type_readout" "new.current_descriptor|new.current_result|descriptor.mapped" <|
    verifyRecord oldEnv newEnv (inlineAuthorization mapping) oldRecord { newRecord with
      descriptor := some changed
      result := .declaredValidated { certificate with descriptorIdentity := identity } }
  let info ← inEnvironment newEnv <| getConstInfo newRecord.occurrence.realizationName
  let actual := info.type.getAppArgs[2]!
  inEnvironment newEnv do
    unless ← isDefEq (← inferType actual) (← inferType changed) do
      throwError "primitive_mutation_type_changed"
  let primitive ← rejected "same_type_primitive" "new.current_result|actual.new|actual.mapped" <|
    verifyRecord oldEnv newEnv (inlineAuthorization mapping) oldRecord { newRecord with
      result := .declaredValidated { certificate with actualIdentity := identity } }
  let alternate := mkAppN (mkConst ``alternativeCut original.getAppFn.constLevels!) original.getAppArgs
  inEnvironment newEnv do
    unless ← isDefEq (← inferType original) (← inferType alternate) do
      throwError "template_mutation_type_changed"
  let .ok (alternateIdentity, _) ← inEnvironment newEnv <| TemplateAudit.rawIdentity
      newRecord.occurrence.levelParams alternate | throwError "alternate_fingerprint_failed"
  let template ← rejected "same_type_template_selection" "new.current_descriptor|descriptor.new|unregistered_template" <|
    verifyRecord oldEnv newEnv (inlineAuthorization mapping) oldRecord { newRecord with
      descriptor := some alternate
      result := .declaredValidated { certificate with descriptorIdentity := alternateIdentity } }
  let owner ← rejected "unauthorized_owner" "new.current_event_count|dtr.event_owner|unit_algorithm" <|
    verifyRecord oldEnv newEnv (inlineAuthorization mapping) oldRecord { newRecord with
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
  let emitted ← match output.getObjValAs? (Array (String × String)) "name_mapping" with
    | .ok emitted => pure emitted
    | .error _ => do
      logError "[FAIL] comparator_rejects_unauthorized_mapping"
      pure #[]
  unless emitted.all (fun (a,b) =>
      (a.startsWith "Reg." || a.startsWith "_private.Reg.") &&
      (b.startsWith "Reg." || b.startsWith "_private.Reg.")) do
    logError "[FAIL] comparator_rejects_unauthorized_mapping"
  logInfo "[PASS] comparator_rejects_unauthorized_mapping"
  let support ← rejected "prefix_unmigrated_collision" "constant_collision" do
    let env ← getEnv
    let a := `Reg.MappingFixture.Source.x
    let b := `Reg.MappingFixture.Target.x
    unless env.contains a && env.contains b do throwError "collision_fixture_constants_missing"
    validateSupportImages #[(`Reg.MappingFixture.Source, `Reg.MappingFixture.Target)] #[a, b]
    return Json.null
  let key := newRecord.occurrence.key
  let other := { newRecord with occurrence := { newRecord.occurrence with
    key := { key with catalog := `anotherCatalog } } }
  let input ← uniqueInput (RegistrationInputs.owned oldEnv) oldRecord.occurrence.key
  let inputOther := { input with entry := { input.entry with
    localRegistrationNames := false
    catalogId := `anotherCatalog
    objectArenaName := oldRecord.occurrence.key.objectArena } }
  let inputOwner := input.entry.registrationModuleName
  let inputs := #[(inputOwner, input), (inputOwner, inputOther)]
  let inputCorrect ← tryCatchRuntimeEx (do
      let found ← uniqueInput inputs (inputKey inputOther.entry)
      pure (found.entry.catalogId == `anotherCatalog)) (fun _ => pure false)
  let inputDuplicate ← rejected "duplicate_input_key" "input_key_count" do
    discard <| uniqueInput #[(inputOwner, input), (inputOwner, input)] (inputKey input.entry)
    return Json.null
  let inputMissing ← rejected "missing_input_key" "input_key_count|input_missing" do
    discard <| uniqueInput #[(inputOwner, input)] (inputKey inputOther.entry)
    return Json.null
  let correct ← tryCatchRuntimeEx (do
      let paired ← pairRecords #[] #[other, newRecord] #[newRecord, other]
      pure (paired.size == 2 && paired[0]!.2.occurrence.key.catalog == `anotherCatalog))
    (fun _ => pure false)
  let correct := correct && inputCorrect
  unless correct do logError "[FAIL] comparator_pairs_same_theorem_multiple_catalogs"
  if correct then logInfo "[PASS] comparator_pairs_same_theorem_multiple_catalogs"
  let duplicate ← rejected "duplicate_occurrence_key" "duplicate_key" do
    discard <| pairRecords #[] #[newRecord] #[newRecord, newRecord]
    return Json.null
  let missing ← rejected "missing_occurrence_key" "missing_key|mapped_duplicate_key|unconsumed_record" do
    discard <| pairRecords #[] #[newRecord, other] #[newRecord]
    return Json.null
  let unconsumed ← rejected "unconsumed_occurrence" "unconsumed_record" do
    discard <| pairRecords #[] #[newRecord] #[newRecord, other]
    return Json.null
  return #[stale, environmentClaim, readout, primitive, template, owner, collision, injection, support,
    duplicate, missing, unconsumed, inputDuplicate, inputMissing,
    Json.mkObj [("test", toJson "unauthorized_mapping"), ("verified", toJson true)],
    Json.mkObj [("test", toJson "json_field_roles"), ("verified", toJson true)]]

end LeanInformationAuditRegTests.ContractMapping
