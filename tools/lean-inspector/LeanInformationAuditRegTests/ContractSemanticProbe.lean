import LeanInformationAuditRegTests.ContractMapping
import LeanInformationAudit.ContractPrototype.UnresolvedEquivalence
import Reg.ContractPrototype.Inline
import Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
import Reg.ContractPrototype.ValidWitness
import Reg.ContractPrototype.Controls.Witness

open Lean Meta Elab Command LeanInformationAudit
open ContractPrototype.Equivalence LeanInformationAuditRegTests.ContractMapping

run_cmd do
  let env := (← getEnv).setExporting false
  setEnv env
  liftTermElabM do
    let original := `Reg.D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
    let prototype := `Reg.ContractPrototype.Inline
    let control := `Reg.ContractPrototype.Controls.Witness
    let candidate := `Reg.ContractPrototype.ValidWitness
    let reports ← ContractPrototype.reports #[original, prototype, control, candidate]
    let mode := (← IO.getEnv "STRATALINT_CONTRACT_SEMANTIC_MUTATION").getD "control"
    let records (env : Environment) (owner : Name) :=
      (TemplateBinding.records env).filter (·.occurrence.key.registrationModule == owner)
    if mode == "bridge" then
      let some (_, _, oldEnv) := reports[0]? | throwError "report_missing"
      let some (_, _, newEnv) := reports[1]? | throwError "report_missing"
      discard <| rejected "generated_bridge_rename" "unauthorized_generated_bridge" <|
        verifyRecord oldEnv newEnv (inlineAuthorization #[(original, prototype),
          (`Reg.Support.BoundedRunSpace, `Reg.ContractPrototype.Templates.Cut)])
          (records oldEnv original)[0]! (records newEnv prototype)[0]!
    else if mode == "undeclared" then
      let some (_, _, oldEnv) := reports[2]? | throwError "report_missing"
      let some (_, _, newEnv) := reports[3]? | throwError "report_missing"
      let missing (env : Environment) (owner : Name) := (records env owner).find?
        (·.occurrence.key.theoremName == `Reg.ContractPrototype.Fixtures.Witness.third)
      let some oldRecord := missing oldEnv control | throwError "missing_control_third"
      let some newRecord := missing newEnv candidate | throwError "missing_candidate_third"
      discard <| rejected "undeclared_primitive_change" "undeclared.actual" <|
        verifyMissingRecord oldEnv newEnv {
          owners := #[(control, candidate)]
          generatedBridges := #[(`Reg.ContractPrototype.Fixtures.Witness.thirdBridge,
            `Reg.ContractPrototype.ValidWitness.changedBridge)] } oldRecord newRecord
    else if mode != "control" then throwError "unknown_semantic_mutation"
    let provenance := Json.mkObj [("argument_inputs", Json.arr #[]), ("extraction_inputs", Json.arr #[]),
      ("plan_identity", toJson "plan"), ("rule", toJson "E5.unsaturated_definition"),
      ("site", toJson "named.site"), ("template_key", toJson "template")]
    let prefixText := "IE-C050 ClosedTruthReadout key=x reason=unclassified_form "
    let unknownFields := Json.mkObj ((provenance.getObj?.toOption.get!).toArray.toList ++
      [("future_field", toJson true)])
    let diagnostics := #["IE-C050 ClosedTruthReadout key=x reason=incomplete_closure provenance=null",
      prefixText ++ "provenance=" ++ unknownFields.compress,
      prefixText ++ "provenance=" ++ (Json.mkObj [("site", toJson "named.site"),
        ("rule", toJson "E5.unsaturated_definition")]).compress,
      "IE-C099 ClosedTruthReadout key=x reason=unclassified_form provenance=" ++ provenance.compress]
    let mut allRejected := true
    for diagnostic in diagnostics do
      let error ← tryCatchRuntimeEx (do
        ContractPrototype.UnresolvedEquivalence.requireSupportedDiagnostic diagnostic
        pure none) (fun error => pure (some error))
      match error with
      | none => allRejected := false
      | some error =>
        unless (← error.toMessageData.toString).contains "unsupported_form" do allRejected := false
    if allRejected then logInfo "[PASS] comparator_rejects_unsupported_unresolved_form"
    else logError "[FAIL] comparator_rejects_unsupported_unresolved_form"
    setEnv env
