/- GID: D5/S3/Analytic/LogSquareBound
   generality: G
   mirror-B: D5/B/S3/Analytic/LogSquareBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A power majorant bounds the squared logarithm on the positive half-line. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A global power majorant for the squared logarithm. -/

namespace D5.S3.Analytic.LogSquareBound

theorem log_square_bound (x : ℝ) (hx : 0 < x) :
    (Real.log x)^2 ≤ 16 * x ^ (-1/2 : ℝ) + x^2 := by
  by_cases h1 : x ≤ 1
  · have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le h1
    have h := Real.log_le_rpow_div (inv_nonneg.mpr hx.le) (by norm_num : (0 : ℝ) < 1/4)
    rw [Real.log_inv, ← Real.rpow_neg_eq_inv_rpow] at h
    have hp : 0 ≤ x ^ (-1/4 : ℝ) := Real.rpow_nonneg hx.le _
    have he : (x ^ (-1/4 : ℝ))^2 = x ^ (-1/2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    have hb : (Real.log x)^2 ≤ 16 * (x ^ (-1/4 : ℝ))^2 := by
      norm_num at h; nlinarith
    rw [he] at hb
    nlinarith [sq_nonneg x]
  · have hl : 0 ≤ Real.log x := Real.log_nonneg (le_of_not_ge h1)
    have hb := Real.log_le_sub_one_of_pos hx
    have hp : 0 ≤ x ^ (-1/2 : ℝ) := Real.rpow_nonneg hx.le _
    nlinarith

end D5.S3.Analytic.LogSquareBound
