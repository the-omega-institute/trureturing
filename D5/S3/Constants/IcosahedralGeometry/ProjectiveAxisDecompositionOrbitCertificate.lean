/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionOrbitCertificate
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionOrbitCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite certificate computes the three projective axis orbits and stabilizer orders. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionAxisClasses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

/-- The displayed projective matrix group has the source-stated order 60. -/
theorem icosahedralGroup_card : Fintype.card IcosahedralGroup = 60 := by
  rw [card_alternatingGroup]
  norm_num

set_option maxHeartbeats 4000000 in
-- The certificate exhaustively checks 31 axes against the 60-element action.
set_option maxRecDepth 100000 in
theorem chartFiniteAxisCertificate :
    chartFivefoldAxes ∩ chartThreefoldAxes = ∅ ∧
      chartFivefoldAxes ∩ chartTwofoldAxes = ∅ ∧
      chartThreefoldAxes ∩ chartTwofoldAxes = ∅ ∧
      chartFivefoldAxes ∪ chartThreefoldAxes ∪ chartTwofoldAxes = Finset.univ ∧
      chartFivefoldAxes.card = 6 ∧
      chartThreefoldAxes.card = 10 ∧
      chartTwofoldAxes.card = 15 ∧
      (∀ p ∈ chartFivefoldAxes, chartAxisOrbit p = chartFivefoldAxes) ∧
      (∀ p ∈ chartThreefoldAxes, chartAxisOrbit p = chartThreefoldAxes) ∧
      (∀ p ∈ chartTwofoldAxes, chartAxisOrbit p = chartTwofoldAxes) ∧
      (∀ p ∈ chartFivefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 10) ∧
      (∀ p ∈ chartThreefoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 6) ∧
      (∀ p ∈ chartTwofoldAxes,
        Fintype.card (MulAction.stabilizer IcosahedralGroup p) = 4) := by
  decide

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
