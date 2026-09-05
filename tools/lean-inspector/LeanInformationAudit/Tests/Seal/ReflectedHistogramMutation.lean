import LeanInformationAudit.ProofBuilder

open Lean
open Lean.Elab.Command

namespace LeanInformationAudit.Tests.Seal.ReflectedHistogramMutation

/-- error: IE-C009 ProofConstructionFailed: LeanInformationAudit.Tests.Seal.ReflectedHistogramMutation.target
role histogram mismatch -/
#guard_msgs (error) in
run_cmd do
  match LeanInformationAudit.validateRoleHistogram
      `LeanInformationAudit.Tests.Seal.ReflectedHistogramMutation.target 2 #[1, 0] with
  | .ok () => pure ()
  | .error message => throwError message

end LeanInformationAudit.Tests.Seal.ReflectedHistogramMutation
