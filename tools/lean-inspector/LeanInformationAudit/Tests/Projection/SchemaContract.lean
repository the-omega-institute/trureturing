import LeanInformationAudit.Projection.ProjectionSchema

open Lean LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection

/-- error: IE-C041 IncompleteKernelProjectionBoundary root=Root catalog=Catalog missing=["absent"] -/
#guard_msgs in
run_cmd do
  let projection : KernelProjectionRecord := {
    leaveOneOut := #[{
      theoremName := `member, node := "absent", uniqueCaptureCount := 0,
      certificate := `certificate }]
  }
  match projection.validateReferences `Root `Catalog with
  | .ok () => pure ()
  | .error message => throwError message

/-- error: IE-C043 KernelProjectionUsedForAdmission consumer=gate field=node_key root=Root catalog=Catalog -/
#guard_msgs in
run_cmd do
  match rejectProjectionAdmission `gate "node_key" `Root `Catalog with
  | .ok () => pure ()
  | .error message => throwError message

run_cmd do
  let projection : KernelProjectionRecord := {}
  let actual := projection.toJson.getObjValAs? String "projection_kind"
  unless actual.toOption == some "boundary-and-certified-chains" do
    throwError "projection kind mismatch"
  let keys := projection.toJson.getObj?.toOption.get!.toArray.map (·.1) |>.qsort (· < ·)
  let expected := #["projection_kind", "complete_lattice_materialized", "nodes", "edges",
    "collapsed_additions", "leave_one_out", "certified_chains", "refinement_matrix",
    "overlap_matrix", "multiplicity_spectrum", "redundant_indices", "verdict",
    "certificates"].qsort (· < ·)
  unless keys == expected do throwError "projection key set mismatch"

end LeanInformationAudit.Tests.Projection
