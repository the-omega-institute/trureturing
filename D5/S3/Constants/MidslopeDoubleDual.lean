/- GID: D5/S3/Constants/MidslopeDoubleDual
   generality: G
   mirror-B: D5/B/S3/Constants/MidslopeDoubleDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relate affine midslope duality to curvature doubling for the arithmetic-geometric pair. -/

/- Library-search audit trail (2026-08-12):
   * Searches for `MidslopeDouble`, `DoubleDual`, `DualLaw`, `CurvatureDual`,
     `curvature.*dual`, and `dual.*curvature` found no matching theorem in pinned Mathlib.
   * `Real.log_lt_sub_one_of_pos` supplies the only denominator side condition.
   * The imported exact-value module proves the arithmetic and geometric midslope values;
     this file wraps those results and does not repeat their integral evaluations.
-/

import D5.S3.Constants.MidslopeCurvatureValues

namespace D5.S3.Constants.MidslopeDoubleDual

open D5.S3.Constants.MidslopeCurvature
open D5.S3.Constants.MidslopeCurvatureValues

/-- The curvature coefficient associated with a midslope value. -/
noncomputable def curvatureCoefficient (j : Real) : Real := 1 / (1 + j)

/-- Away from the pole at `-1`, affine duality of midslope values is equivalent to doubling
the curvature coefficient in the reverse direction. -/
theorem affine_dual_iff_curvature_double {j j' : Real}
    (hj : Ne (1 + j) 0) (hj' : Ne (1 + j') 0) :
    j' = 2 * j + 1 <->
      curvatureCoefficient j = 2 * curvatureCoefficient j' := by
  unfold curvatureCoefficient
  constructor
  · intro hdual
    field_simp [hj, hj']
    linarith
  · intro hcurvature
    field_simp [hj, hj'] at hcurvature
    linarith

/-- For the arithmetic and geometric midslope values, the affine double-dual law is exactly the
reverse doubling law for their curvature coefficients. This is the first of the two source pairs;
the separate logarithmic-harmonic pair is not covered here. -/
theorem arithmetic_geometric_double_dual :
    J_zero = 2 * J_one + 1 <->
      curvatureCoefficient J_one = 2 * curvatureCoefficient J_zero := by
  apply affine_dual_iff_curvature_double
  · rw [J_one_eq_neg_log_two]
    have hlog : Real.log 2 < 1 := by
      convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : Real) < 2) (by norm_num) using 1 <;>
        norm_num
    linarith
  · rw [J_zero_eq_one_sub_two_log_two]
    have hlog : Real.log 2 < 1 := by
      convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : Real) < 2) (by norm_num) using 1 <;>
        norm_num
    linarith

/- Both sides of the equivalence hold for the imported exact values. -/
example : J_zero = 2 * J_one + 1 := by
  rw [J_zero_eq_one_sub_two_log_two, J_one_eq_neg_log_two]
  ring

example : curvatureCoefficient J_one = 2 * curvatureCoefficient J_zero := by
  exact arithmetic_geometric_double_dual.mp (by
    rw [J_zero_eq_one_sub_two_log_two, J_one_eq_neg_log_two]
    ring)

#print axioms arithmetic_geometric_double_dual

end D5.S3.Constants.MidslopeDoubleDual
