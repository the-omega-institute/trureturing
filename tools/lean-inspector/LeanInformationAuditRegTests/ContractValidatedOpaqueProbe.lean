import LeanInformationAuditRegTests.ContractMapping
import Reg.ContractPrototype.Controls.ValidatedOpaque
import Reg.ContractPrototype.ValidatedOpaque

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

run_cmd do
  let saved := (← getEnv).setExporting false
  setEnv saved
  liftTermElabM do
    let oldRoot := `Reg.ContractPrototype.Controls.ValidatedOpaque
    let newRoot := `Reg.ContractPrototype.ValidatedOpaque
    let reports ← ContractPrototype.reports #[oldRoot, newRoot]
    let some (_, _, oldEnv) := reports[0]? | throwError "old_report_missing"
    let some (_, _, newEnv) := reports[1]? | throwError "new_report_missing"
    let record (env : Environment) (owner : Name) :=
      ((TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner))[0]!
    let oldRecord := record oldEnv oldRoot
    let newRecord := record newEnv newRoot
    unless (oldRecord.result matches .declaredValidated _) &&
        (newRecord.result matches .declaredValidated _) do
      throwError "validated_opaque_state: {← TemplateBinding.recordJson oldRecord} / {← TemplateBinding.recordJson newRecord}"
    verifyCurrentRecord "old-control" oldEnv oldRecord
    verifyCurrentRecord "new-control" newEnv newRecord
    let mode := (← IO.getEnv "STRATALINT_CONTRACT_VALIDATED_OPAQUE_MUTATION").getD "control"
    let bit (env : Environment) (owner : Name) : MetaM Bool := inEnvironment env do
      let name := owner.str "hiddenBit"
      let .opaqueInfo info ← getConstInfo name | throwError "opaque_bit_kind"
      if info.value.isConstOf ``Bool.false then return false
      if info.value.isConstOf ``Bool.true then return true
      throwError "opaque_bit_nonliteral"
    unless (← bit oldEnv `Reg.ContractPrototype.Inputs.ValidatedOpaqueOld) == (mode == "old") &&
        (← bit newEnv `Reg.ContractPrototype.Inputs.ValidatedOpaqueNew) == (mode == "new") do throwError "opaque_mutation_not_exercised"
    let authorization : Authorization := {
      owners := #[(oldRoot, newRoot),
        (`Reg.Support.BoundedRunSpace, `Reg.ContractPrototype.Templates.Cut),
        (`Reg.ContractPrototype.Inputs.ValidatedOpaqueOld, `Reg.ContractPrototype.Inputs.ValidatedOpaqueNew),
        (`ContractPrototypeFixtures.ValidatedOpaqueOld, `ContractPrototypeFixtures.ValidatedOpaqueNew)]
      generatedBridges := #[(oldRecord.occurrence.realizationName, newRoot.str "bridge")] }
    if mode == "control" then
      discard <| verifyRecord oldEnv newEnv authorization oldRecord newRecord
      logInfo "[PASS] validated_opaque_equal_control"
    else
      discard <| rejected ("validated_opaque_" ++ mode) "dependency.mapped.body|dependency_count|dependency_enumeration" <|
        verifyRecord oldEnv newEnv authorization oldRecord newRecord
    setEnv saved
