import LeanInformationAudit.Tests.RegistrationGates.DependentFamilyControls

open Lean Elab Command LeanInformationAudit
open LeanInformationAudit.Tests.DependentFamily
open LeanInformationAudit.Tests.DependentFamilyControls
open D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation

register_information_family history_law_conditional_expectation in weakenedArena
  readout via (template signature (fun _ _ ω => ω.2) Empty.elim) realization weakenedRegistration
  escape from coordinates [0, 1, 11]
  state ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
  output ["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg", "arg"]
  escape continues (open)

run_cmd do
  let env ← getEnv
  let some row := (TemplateBinding.records env).find?
      (·.occurrence.key.registrationModule == env.header.mainModule)
    | throwError "missing unresolved family"
  match row.result with
  | .declaredUnresolved diagnostic =>
    unless (diagnostic.splitOn "rule=family.registration.exact_source_law site=").length == 2 &&
        row.escape.family.isNone && row.escape.continuation == some { kind := "open" } do
      throwError "wrong unresolved family result: {diagnostic}"
    logInfo "[PASS] unresolved_family_exact_source_law_preserved"
  | _ => throwError "weakened family did not remain unresolved"
