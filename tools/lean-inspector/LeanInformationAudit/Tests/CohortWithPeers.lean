import LeanInformationAudit.Tests.CohortTarget
import LeanInformationAudit.Tests.CohortPeer
import LeanInformationAudit.Tests.CohortOther
import LeanInformationAudit.Tests.CohortView

/-! The target loaded with two registering peers it does not import. The peer
enrolls `iffRealization`, which the target names but does not enroll, and
enrolls `cutRealization` a second time. See `CohortView`. -/

open LeanInformationAudit.Tests.CohortView in
/-- info: [PASS] report_target_cohort_independent cases=5 digest=16106520453234887392 records=statement:declared_validated,unenrolled:declared_unresolved:unregistered_template -/
#guard_msgs (info, drop warning) in
run_meta observe #[
  ("peers_loaded_not_requested", #[target]),
  ("peers_requested", #[target, peer, other]),
  ("peers_first", #[peer, other, target]),
  ("batch_99", ← batch 99 #[peer, other]),
  ("batch_100", ← batch 100 #[peer, other])]
