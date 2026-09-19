import LeanInformationAudit.Tests.RegistrationGates.DependentFamilyUnicode

open Lean Elab Command LeanInformationAudit
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

register_information_family history_law_conditional_expectation
  in LeanInformationAudit.Tests.DependentFamilyUnicode.arena
  readout via (LeanInformationAudit.Tests.DependentFamily.template
    LeanInformationAudit.Tests.DependentFamilyUnicode.signature (fun _ _ x => x) Empty.elim)
  realization LeanInformationAudit.Tests.DependentFamilyUnicode.registration
  escape from coordinates [0, 1, 11]
  state ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
  output ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg"]
  escape continues (open)

run_cmd do
  let env ← getEnv
  let some row := (TemplateBinding.records env).find?
      (·.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "missing wrong-registration family"
  match row.result with
  | .declaredUnresolved diagnostic =>
    unless (diagnostic.splitOn "family.registration.source_law").length > 1 do
      throwError "unexpected diagnostic: {diagnostic}"
    logInfo "[PASS] wrong_registration_retained_unresolved"
  | _ => throwError "wrong-registration family was not unresolved"
