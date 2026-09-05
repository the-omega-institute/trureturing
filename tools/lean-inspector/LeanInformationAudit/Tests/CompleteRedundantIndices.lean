import LeanInformationAudit.ProofBuilder

open LeanInformationAudit

namespace LeanInformationAudit.Tests.CompleteRedundantIndices

/-- error: IE-C033 IncompleteRedundantIndexSet key=fixtureRoot/fixtureCatalog expected=[0,1,2] certified=[0] phase=first-zero -/
#guard_msgs (error) in
run_cmd do
  match validateRedundantIndices `fixtureRoot `fixtureCatalog #[0, 1, 2] #[0]
      "first-zero" with
  | .ok () => pure ()
  | .error message => throwError message

end LeanInformationAudit.Tests.CompleteRedundantIndices
