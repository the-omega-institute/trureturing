import LeanInformationAudit.Tests.CohortOther
import LeanInformationAudit.Tests.CohortPeer
import LeanInformationAudit.Tests.CohortTarget
import LeanInformationAudit.Tests.CohortView

/-! The peers imported before the target, and requested around it. See `CohortView`. -/

open LeanInformationAudit.Tests.CohortView in
/-- info: [PASS] report_target_cohort_independent cases=2 digest=16106520453234887392 records=statement:declared_validated,unenrolled:declared_unresolved:unregistered_template -/
#guard_msgs (info, drop warning) in
run_meta observe #[
  ("import_and_request_permuted", #[other, target, peer]),
  ("peer_only_neighbour", #[peer, target])]
