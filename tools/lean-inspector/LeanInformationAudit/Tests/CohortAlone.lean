import LeanInformationAudit.Tests.CohortTarget
import LeanInformationAudit.Tests.CohortView

/-! The target loaded without any registering peer. See `CohortView`. -/

open LeanInformationAudit.Tests.CohortView in
/-- info: [PASS] report_target_cohort_independent cases=3 digest=9821773128832720548 records=statement:declared_validated,unenrolled:declared_unresolved:unregistered_template -/
#guard_msgs (info, drop warning) in
run_meta observe #[
  ("alone", #[target]),
  ("batch_99", ← batch 99 #[]),
  ("batch_100", ← batch 100 #[])]
