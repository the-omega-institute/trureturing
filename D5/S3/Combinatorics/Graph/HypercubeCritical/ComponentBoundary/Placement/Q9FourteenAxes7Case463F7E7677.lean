import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

/-! Refutation of a seven-axis orbit with fourteen contact masks. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

set_option maxHeartbeats 0 in
-- Replay uses the input clauses justified by the specified family.
replay_fifteen_masks fourteenSevenImpossible0 [6, 10, 18, 33, 34, 36, 40, 48, 65, 66, 68, 72, 80] fingerprint 1953266093771582543 certificate
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FourteenAxes7Case463F7E7677.result.json")

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay
