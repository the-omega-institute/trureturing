import LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaOIProbe

open Lean LeanInformationAudit
run_meta do
  let rows ← TemplateBinding.assessJoined
  let selected := rows.filter (fun r => r.occurrence.key.registrationModule ==
    `LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaOIProbe)
  unless selected.size == 7 do throwError "[FAIL] SevenRegistrations: wrong occurrence count"
  let mut validated := 0
  for row in selected do
    let state := match row.result with
      | .declaredValidated _ => "declared_validated"
      | .declaredUnresolved _ => "declared_unresolved"
      | .undeclared => "undeclared"
    let reading := Json.mkObj [
      ("theorem", toJson row.occurrence.key.theoremName.toString),
      ("state", toJson state),
      ("statement_identity", toJson row.occurrence.statementIdentity)]
    logInfo m!"BINDING_PROBE {reading.compress}"
    if row.result matches .declaredValidated _ then
      validated := validated + 1
  unless validated == 7 do
    throwError "[FAIL] SevenRegistrations: {validated}/7 validated"
  logInfo "[PASS] SevenRegistrations: 7/7 validated"
  for target in #[
      ``D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      ``D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation] do
    let some row := rows.find? (fun r => r.occurrence.key.theoremName == target &&
        r.occurrence.key.registrationModule == `LeanInformationAudit.Tests.RegistrationGates.StatementAliasMemo.SharedArenaOIProbe)
      | throwError "missing OI occurrence"
    unless row.result matches .declaredValidated _ do
      throwError "POSITIVE_OI_NOT_VALIDATED:{target}"
    logInfo m!"[PASS] OIRegistration_{target.getString!}: declared_validated"
