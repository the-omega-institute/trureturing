import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

/-! Refutation of a seven-axis orbit with fourteen contact masks. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option Elab.async false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay

set_option maxHeartbeats 0 in
-- Replay uses the input clauses justified by the specified family.
replay_fifteen_masks fourteenSevenImpossible24 [5, 10, 20, 24, 33, 36, 40, 48, 66, 68, 72, 80, 96] fingerprint 5091401743866623304 certificate
  (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FourteenAxes7Case46555A7577.result.json")

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay
