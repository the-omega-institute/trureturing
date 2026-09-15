import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredEnrollmentInputs
open Lean Elab Command TemplateAudit

elab "observe_enrollment_inputs" : command => do
  let saved ← get
  let name := ``DeclaredTemplates.symbolicPointwise
  let bounded ← enroll name
  let issued := (selectedPlan (← getEnv) name).isOk
  set saved
  let positive := s!"[{if bounded.isOk && issued then "PASS" else "FAIL"}] bounded_complete_enrollment_accepted"
  elabCommand (← `(command| set_option informationTemplate.work 0))
  let exhausted ← enroll name
  let noEvidence := !(selectedPlan (← getEnv) name).isOk
  -- The first native dependency must serialize its type within the quota.
  let incomplete := exhausted matches .error "incomplete_closure:E7.type_identity"
  set saved
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
  logInfo positive
  logInfo budget
  logInfo m!"[{if incomplete && noEvidence then "PASS" else "FAIL"}] enrollment_missing_body_incomplete result={repr missing}"

observe_enrollment_inputs

end LeanInformationAudit.Tests.DeclaredEnrollmentInputs
