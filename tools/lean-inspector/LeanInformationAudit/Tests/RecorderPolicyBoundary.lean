import LeanInformationAudit.Tests.RecorderPolicyInputs
import LeanInformationAudit.Tests.Assessment

/-! The recorder is policy-free; admission is the report's. The imported fixture
module compiled against the Interface package only, and its two recorded inputs
violate report-owned rules. Here the report's assessment service rejects each
with the diagnostic its rule defines, and the report's replay entry rejects the
module as a whole without leaving any registry entry or generated declaration. -/

namespace LeanInformationAudit.Tests.RecorderPolicyBoundary
open Lean Elab Command

private def producer : Name := `LeanInformationAudit.Tests.RecorderPolicyInputs

/-- info: [PASS] recorder_records_policy_violating_inputs count=2 -/
#guard_msgs in
run_cmd do
  let recorded := (RegistrationInputs.owned (← getEnv)).filter (·.1 == producer)
    |>.map (·.2.entry.theoremName)
  unless recorded == #[``RecorderPolicyInputs.reserved.__catalog_irredundant,
      ``RecorderPolicyInputs.lifted] do
    throwError "[FAIL] recorder_records_policy_violating_inputs {recorded}"
  unless (InformationRegistry.entries (← getEnv)).isEmpty do
    throwError "[FAIL] recorder_assessed_at_compile_time"
  logInfo m!"[PASS] recorder_records_policy_violating_inputs count={recorded.size}"

/--
info: LeanInformationAudit.Tests.RecorderPolicyInputs.reserved.__catalog_irredundant: IE-C011 GeneratedCertificateRegistered: LeanInformationAudit.Tests.RecorderPolicyInputs.reserved.__catalog_irredundant
---
info: LeanInformationAudit.Tests.RecorderPolicyInputs.lifted: P1.RigidUniverseMismatch: arena must have three zero universe levels
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  for (owner, input) in RegistrationInputs.owned env do
    unless owner == producer do continue
    let outcome ← try
      GeneratedDeclarations.withOwner owner <| assessRecordedEntry owner input
      pure "accepted"
    catch error => pure (← error.toMessageData.toString)
    unless (InformationRegistry.entries (← getEnv)).isEmpty &&
        (GeneratedDeclarations.entries (← getEnv)).isEmpty do
      throwError "[FAIL] rejected_input_left_assessment_state {input.entry.theoremName}"
    setEnv env
    logInfo m!"{input.entry.theoremName}: {outcome}"

/-- info: [PASS] report_replay_rejects_policy_violating_module -/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let outcome ← try
    liftTermElabM <| assessRecordedRegistrations producer
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless outcome.any (·.startsWith "IE-C011 GeneratedCertificateRegistered:") &&
      (InformationRegistry.entries (← getEnv)).isEmpty do
    throwError "[FAIL] report_replay_rejects_policy_violating_module {outcome}"
  setEnv env
  logInfo "[PASS] report_replay_rejects_policy_violating_module"

end LeanInformationAudit.Tests.RecorderPolicyBoundary
