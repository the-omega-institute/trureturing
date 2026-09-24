import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredEnrollmentInputs
open Lean Elab Command TemplateAudit

elab "observe_enrollment_inputs" : command => do
  let saved ← get
  let name := ``DeclaredTemplates.symbolicPointwise
  let bounded ← enroll name
  let issued := (selectedPlan (← getEnv) name).isOk
  set saved
  let positiveOk := bounded.isOk && issued
  let positive := s!"[{if bounded.isOk && issued then "PASS" else "FAIL"}] bounded_complete_enrollment_accepted"
  elabCommand (← `(command| set_option informationTemplate.work 0))
  let exhausted ← enroll name
  let noEvidence := !(selectedPlan (← getEnv) name).isOk
  -- Typed proof erasure consumes quota before the first identity is serialized.
  let incomplete := exhausted matches .error "incomplete_closure:E8.erasure_work"
  set saved
  let budgetOk := incomplete && noEvidence
  let budget := s!"[{if incomplete && noEvidence then "PASS" else "FAIL"}] enrollment_budget_incomplete result={repr exhausted}"
  -- Missing native input at the checker boundary. No fabricated successful
  -- definition or axiom stands in for an unavailable template body.
  let missingName := `LeanInformationAudit.Tests.DeclaredEnrollmentInputs.missingNativeBody
  unless !(← getEnv).contains missingName do throwError "setup: missing body unexpectedly exists"
  let missing ← enroll missingName
  let noEvidence := !(selectedPlan (← getEnv) missingName).isOk
  let incomplete := match missing with
    | .error reason => reason.startsWith "incomplete_closure:E8.elaboration:"
    | .ok () => false
  set saved
  (if positiveOk then logInfo else logError) positive
  (if budgetOk then logInfo else logError) budget
  (if incomplete && noEvidence then logInfo else logError) m!"[{if incomplete && noEvidence then "PASS" else "FAIL"}] enrollment_missing_body_incomplete result={repr missing}"

observe_enrollment_inputs

end LeanInformationAudit.Tests.DeclaredEnrollmentInputs
