import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

/-! Refutation of a seven-axis orbit with fourteen contact masks. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

set_option maxHeartbeats 0 in
-- Replay uses the input clauses justified by the specified family.
replay_fifteen_masks fourteenSevenImpossible5 [6, 10, 17, 18, 20, 33, 34, 40, 66, 68, 72, 80, 96] fingerprint 2750602992166545333 certificate
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FourteenAxes7Case4645687E77.result.json")

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay
