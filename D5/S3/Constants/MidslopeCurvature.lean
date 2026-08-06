/- GID: D5/S3/Constants/MidslopeCurvature
   generality: G
   mirror-B: D5/B/S3/Constants/MidslopeCurvature
   mirror-E: none(waiver:exact-closed-integral-identities-only)
   anchors: []
   digest: Evaluate the harmonic and arithmetic midslope-curvature integrals exactly. -/

import D5.S3.Constants.PowerMeanKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Interval

namespace D5.S3.Constants.MidslopeCurvature

open D5.S3.Constants.PowerMeanKernel

/-- The midslope-curvature integral specialized to the harmonic mean. -/
noncomputable def J_neg_one : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ((1 - t) / t ^ 2) *
      (1 / (2 * meanNegOne ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))

/-- The midslope-curvature integral specialized to the arithmetic mean. -/
noncomputable def J_one : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ((1 - t) / t ^ 2) *
      (1 / (2 * meanOne ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2))

/-- The harmonic-mean midslope curvature vanishes. -/
theorem J_neg_one_eq_zero : J_neg_one = 0 := by
  rw [J_neg_one]
  calc
    _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change
        (1 - t) / t ^ 2 *
            (1 / (2 * meanNegOne ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2)) =
          0
      have hmean :
          2 * meanNegOne ((1 + t) / 2) ((1 - t) / 2) = 1 - t ^ 2 := by
        rw [meanNegOne]
        ring
      rw [hmean]
      ring
    _ = 0 := by simp

/-- The arithmetic-mean midslope curvature is minus the natural logarithm of two. -/
theorem J_one_eq_neg_log_two : J_one = -Real.log 2 := by
  rw [J_one]
  calc
    _ = ∫ t in (0 : ℝ)..1, -(1 / (1 + t)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      change
        (1 - t) / t ^ 2 *
            (1 / (2 * meanOne ((1 + t) / 2) ((1 - t) / 2)) - 1 / (1 - t ^ 2)) =
          -(1 / (1 + t))
      have ht_pos : 0 < t := ht.1
      have ht_lt : t < 1 := ht.2
      have ht0 : t ≠ 0 := ne_of_gt ht_pos
      have hadd_pos : 0 < 1 + t := by linarith
      have hsub_pos : 0 < 1 - t ^ 2 := by
        nlinarith [mul_pos (sub_pos.mpr ht_lt) hadd_pos]
      have hmean :
          2 * meanOne ((1 + t) / 2) ((1 - t) / 2) = 1 := by
        rw [meanOne]
        ring
      rw [hmean]
      field_simp [ht0, ne_of_gt hadd_pos, ne_of_gt hsub_pos]
      all_goals ring
    _ = -∫ t in (0 : ℝ)..1, 1 / (1 + t) := by
      rw [intervalIntegral.integral_neg]
    _ = -∫ t in (1 : ℝ)..2, 1 / t := by
      congr 1
      simpa only [zero_add, one_add_one_eq_two, add_comm] using
        (intervalIntegral.integral_comp_add_right
          (f := fun x : ℝ ↦ 1 / x) (a := (0 : ℝ)) (b := 1) 1)
    _ = -Real.log 2 := by
      rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
      norm_num

end D5.S3.Constants.MidslopeCurvature
