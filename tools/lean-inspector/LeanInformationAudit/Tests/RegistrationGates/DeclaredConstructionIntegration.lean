import LeanInformationAudit.Tests.RegistrationGates.DeclaredTemplates

namespace LeanInformationAudit.Tests.DeclaredConstructionIntegration
open Lean Elab Command TemplateAudit

elab "observe_enrollment_construction_quota" : command => do
  let saved ← get
  let bounded ← withScope (fun scope =>
    { scope with opts := scope.opts.set `informationTemplate.work (166000 : Nat) }) <|
    enroll ``DeclaredTemplates.symbolicPointwise
  let rejected := match bounded with
    | .error reason => reason.startsWith "incomplete_closure:E8."
    | _ => false
  set saved
  let positive ← enroll ``DeclaredTemplates.symbolicPointwise
  set saved
  (if rejected then logInfo else logError) m!"[{if rejected then "PASS" else "FAIL"}] enrollment_construction_debit_required"
  (if positive.isOk then logInfo else logError) m!"[{if positive.isOk then "PASS" else "FAIL"}] complete_construction_enrollment_accepted"
  logInfo m!"bounded_enrollment_result={repr bounded}"

observe_enrollment_construction_quota

end LeanInformationAudit.Tests.DeclaredConstructionIntegration
