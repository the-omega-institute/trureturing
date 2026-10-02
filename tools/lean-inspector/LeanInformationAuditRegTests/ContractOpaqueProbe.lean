import LeanInformationAuditRegTests.ContractMapping
import LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
import Reg.ContractPrototype.Controls.Opaque
import Reg.ContractPrototype.Opaque

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

private def withoutClaims (env : Environment) : Environment :=
  (TemplateBinding.ownedEvents env).foldl
    (fun e (_, event) => TemplateBinding.addOccurrence e event)
    (TemplateBinding.resetAssessmentRecords env)

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let oldRoot := `Reg.ContractPrototype.Controls.Opaque
    let newRoot := `Reg.ContractPrototype.Opaque
    let reports ← ContractPrototype.reports #[oldRoot, newRoot]
    let some (_, _, oldEnv) := reports[0]? | throwError "old_report_missing"
    let some (_, _, newEnv) := reports[1]? | throwError "new_report_missing"
    let record (env : Environment) (owner : Name) :=
      ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner))[0]!
    let oldRecord := record oldEnv oldRoot
    let newRecord := record newEnv newRoot
    unless (oldRecord.result matches .declaredUnresolved _) &&
        (newRecord.result matches .declaredUnresolved _) do throwError "opaque_unresolved_state"
    let authorization : Authorization := {
      owners := #[(oldRoot, newRoot),
        (`Reg.Support.CounterexampleRecord, `Reg.ContractPrototype.Templates.Counterexample)] }
    let mode := (← IO.getEnv "STRATALINT_CONTRACT_OPAQUE_MUTATION").getD "control"
    unless #["control", "old", "new", "walk"].contains mode do throwError "unknown_opaque_mutation"
    let mapping ← completeMapping oldEnv newEnv authorization oldRecord newRecord
    let dependencies (env : Environment) (input : BindingRecord) := inEnvironment env do
      let actual := (← getConstInfo input.occurrence.realizationName).type.getAppArgs[2]!
      actualDependencies env input.occurrence actual
    let oldInputs ← dependencies oldEnv oldRecord
    let newInputs ← dependencies newEnv newRecord
    let mapped := (oldInputs.map fun input => { input with
      name := renameName mapping input.name, owner := renameName mapping input.owner }).qsort
        (fun a b => Name.quickLt a.name b.name)
    unless mapped.map (·.name) == newInputs.map (·.name) &&
        mapped.map (·.owner) == newInputs.map (·.owner) do
      throwError "opaque_dependency_members_changed"
    for input in oldInputs do
      let info ← inEnvironment oldEnv <| getConstInfo input.name
      let .ok (typeId, _) ← inEnvironment newEnv <| TemplateAudit.rawIdentity info.levelParams
        (renameExpr mapping info.type) | throwError "opaque_type_identity"
      let some other := newInputs.find? (·.name == renameName mapping input.name)
        | throwError "opaque_dependency_missing"
      unless typeId == other.typeIdentity do throwError "opaque_dependency_type_changed"
    let bit (env : Environment) (owner : Name) : MetaM Bool := inEnvironment env do
      let some name := env.header.moduleData[(env.getModuleIdx? owner).get!.toNat]!.constNames.find?
        (fun name => privateToUserName name == owner.str "hiddenBit") | throwError "opaque_bit_missing"
      let .opaqueInfo info ← getConstInfo name | throwError "opaque_bit_kind"
      unless info.type.isConstOf ``Bool do throwError "opaque_bit_type"
      unless (ConstantInfo.opaqueInfo info).value?.isNone do throwError "opaque_default_not_hidden"
      let body := info.value.consumeMData
      if body.isConstOf ``Bool.false then return false
      if body.isConstOf ``Bool.true then return true
      throwError "opaque_bit_nonliteral"
    let oldBit ← bit oldEnv oldRoot
    let newBit ← bit newEnv newRoot
    unless oldBit == (mode == "old") && newBit == (mode == "new") do
      throwError "opaque_input_mutation_not_exercised"
    if mode == "walk" then
      for (side, env, owner, input) in #[("old", oldEnv, oldRoot, oldRecord),
          ("new", newEnv, newRoot, newRecord)] do
        let some name := env.header.moduleData[(env.getModuleIdx? owner).get!.toNat]!.constNames.find?
          (fun name => privateToUserName name == owner.str "hiddenBit") | throwError "opaque_bit_missing"
        let event := { input.occurrence with statement := mkConst ``True, realizationName := name }
        let inputs ← actualDependencies env event (mkConst name)
        if inputs.any (·.name == ``Bool.false) then
          logInfo m!"[PASS] opaque_repository_body_traversal_{side}"
        else logError m!"[FAIL] opaque_repository_body_traversal_{side}"
    let missingOldEnv := withoutClaims oldEnv
    let missingNewEnv := withoutClaims newEnv
    let oldMissing ← inEnvironment missingOldEnv <| TemplateBinding.assess oldRecord.occurrence none
    let newMissing ← inEnvironment missingNewEnv <| TemplateBinding.assess newRecord.occurrence none
    unless (oldMissing.result matches .undeclared) && (newMissing.result matches .undeclared) do
      throwError "opaque_undeclared_state"
    if mode == "control" || mode == "walk" then
      discard <| ContractPrototype.UnresolvedEquivalence.verifyRecord
        oldEnv newEnv authorization oldRecord newRecord
      discard <| verifyMissingRecord missingOldEnv missingNewEnv authorization oldMissing newMissing
      logInfo "[PASS] opaque_equal_bodies_both_states"
    else
      discard <| rejected ("opaque_unresolved_" ++ mode) "dependency.mapped.body" <|
        ContractPrototype.UnresolvedEquivalence.verifyRecord oldEnv newEnv authorization oldRecord newRecord
      discard <| rejected ("opaque_undeclared_" ++ mode) "dependency.mapped.body" <|
        verifyMissingRecord missingOldEnv missingNewEnv authorization oldMissing newMissing
    logInfo m!"opaque_same_members_and_types: count={oldInputs.size} old={oldBit} new={newBit} mode={mode}"
    setEnv saved
