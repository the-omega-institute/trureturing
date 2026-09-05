/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionChartAction
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionChartAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The explicit word table is certified as an action of A5 on the 31-point chart. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

private theorem actionPermutation_one : actionPermutation 1 = 1 := by
  decide

set_option maxHeartbeats 4000000 in
-- This certificate checks all products in the explicit 60-element chart action.
set_option maxRecDepth 100000 in
private theorem actionPermutation_mul :
    ∀ g h : IcosahedralGroup,
      actionPermutation (g * h) = actionPermutation g * actionPermutation h := by
  decide

instance chartMulAction : MulAction IcosahedralGroup AxisChart where
  smul g p := actionPermutation g p
  one_smul p := by
    change actionPermutation (1 : IcosahedralGroup) p = p
    rw [actionPermutation_one]
    rfl
  mul_smul g h p := by
    change actionPermutation (g * h) p =
      actionPermutation g (actionPermutation h p)
    rw [actionPermutation_mul]
    rfl

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
