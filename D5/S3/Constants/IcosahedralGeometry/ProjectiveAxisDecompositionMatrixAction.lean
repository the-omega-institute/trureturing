/- GID: D5/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionMatrixAction
   generality: I
   mirror-B: D5/B/S3/Constants/IcosahedralGeometry/ProjectiveAxisDecompositionMatrixAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The explicit word matrices are certified as a linear representation of A5 over F5. -/

import D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecompositionChartAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition

private theorem actionMatrix_one : actionMatrix 1 = 1 := by
  decide

set_option maxHeartbeats 12000000 in
-- This certificate checks all products in the explicit 60-element linear representation.
set_option maxRecDepth 100000 in
private theorem actionMatrix_mul :
    ∀ g h : IcosahedralGroup, actionMatrix (g * h) = actionMatrix g * actionMatrix h := by
  intro g h
  fin_cases g <;> fin_cases h <;> decide

/-- The concrete `A₅` representation acts linearly on the source's
three-dimensional `F₅` vector space. -/
instance : DistribMulAction IcosahedralGroup Vector where
  smul g v := (actionMatrix g).mulVec v
  one_smul v := by
    change (actionMatrix 1).mulVec v = v
    rw [actionMatrix_one, Matrix.one_mulVec]
  mul_smul g h v := by
    change (actionMatrix (g * h)).mulVec v =
      (actionMatrix g).mulVec ((actionMatrix h).mulVec v)
    rw [actionMatrix_mul, Matrix.mulVec_mulVec]
  smul_zero g := Matrix.mulVec_zero (actionMatrix g)
  smul_add g v w := Matrix.mulVec_add (actionMatrix g) v w

instance : SMulCommClass IcosahedralGroup F5 Vector where
  smul_comm g a v := by
    change (actionMatrix g).mulVec (a • v) = a • (actionMatrix g).mulVec v
    exact Matrix.mulVec_smul (actionMatrix g) a v

end D5.S3.Constants.IcosahedralGeometry.ProjectiveAxisDecomposition
