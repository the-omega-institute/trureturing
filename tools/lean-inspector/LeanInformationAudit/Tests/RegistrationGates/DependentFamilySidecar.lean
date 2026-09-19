import LeanInformationAudit.Tests.RegistrationGates.DependentFamily

open Lean Elab Command LeanInformationAudit
open LeanInformationAudit.Tests.DependentFamily
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

declare_information_family_binding history_law_conditional_expectation in arena
  readout via (template signature (fun _ _ ω => ω.2) Empty.elim) realization registration
  escape from coordinates [0, 1, 11]
  state ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
  output ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg"]
  escape continues (open)

run_cmd do
  let env ← getEnv
  let some record := (TemplateBinding.records env).find?
      (fun r => r.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "missing family sidecar"
  unless record.occurrence.key.mode == .dependentFamily do throwError "wrong sidecar mode"
  match record.result with
  | .declaredValidated certificate =>
    unless certificate.escape.family.isSome do throwError "missing sidecar origin"
    logInfo "[PASS] unchanged_source_family_sidecar_declared_validated"
  | .declaredUnresolved diagnostic => throwError diagnostic
  | _ => throwError "family sidecar undeclared"
