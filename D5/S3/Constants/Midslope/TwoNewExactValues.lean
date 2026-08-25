/- GID: D5/S3/Constants/Midslope/TwoNewExactValues
   generality: G
   mirror-B: D5/B/S3/Constants/Midslope/TwoNewExactValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two half-parameter midslope curvatures have exact values and affine relations. -/

import D5.S3.Constants.MidslopeCurvatureValues

/- Library-search audit trail (2026-08-25):
   * Exact repository hits `J_half_eq`, `J_half_eq_affine`, and
     `J_neg_half_eq_half_J_zero` prove three of the four public clauses and are
     applied directly.
   * Exact repository hit `J_zero_eq_one_sub_two_log_two` supplies the remaining
     explicit negative-half value from the canonical half-of-zero relation.
   * No frozen declaration packages all four clauses of the source theorem, so
     binding any one hit would under-cover the named conjunction.
   * Pinned Mathlib searches for the two displayed logarithmic values found no
     theorem about these repository-defined curvature integrals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Midslope.TwoNewExactValues

open D5.S3.Constants.MidslopeCurvature
open D5.S3.Constants.MidslopeCurvatureValues

/-- The two half-parameter midslope curvatures have their exact logarithmic
values and satisfy the two stated affine relations. -/
theorem two_new_exact_values :
    J_half = (5 - 12 * Real.log 2) / 6 ∧
      J_neg_half = (1 - 2 * Real.log 2) / 2 ∧
        J_half = (5 / 6) * J_zero + (1 / 3) * J_one ∧
          J_neg_half = J_zero / 2 := by
  refine ⟨J_half_eq, ?_, J_half_eq_affine, J_neg_half_eq_half_J_zero⟩
  calc
    J_neg_half = J_zero / 2 := J_neg_half_eq_half_J_zero
    _ = (1 - 2 * Real.log 2) / 2 := by rw [J_zero_eq_one_sub_two_log_two]

/- The ambient scalar carrier is inhabited. -/
example : ℝ := 0

/- The theorem has no hypotheses; `Unit.unit` witnesses the empty hypothesis context. -/
example : Unit := Unit.unit

#print axioms two_new_exact_values

end D5.S3.Constants.Midslope.TwoNewExactValues
