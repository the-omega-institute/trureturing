/- GID: D5/S1/Digit/CompositeGasContraction
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Companion-root contraction criterion for the digit-gas characteristic root. -/

import D5.S1.Digit.CompositeGasUnit

/-! 本单关闭勘误 §3-E1 之伴根收缩判据，Pisot 语义层（标准定义/不可约档重合性/scholium）留卷面不冒领。 -/

namespace D5.S1.Digit

/-- The companion characteristic root has absolute value `e6Beta c - 1`.

This identity holds for every parameter, including the degenerate `c = 0`
where both sides vanish, so no active-domain hypothesis is recorded here. -/
theorem e6_beta_char_abs (c : ℕ) :
    |e6BetaConjChar c| = e6Beta c - 1 := by
  rw [e6BetaConjChar, abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr (e6_beta_ge_one c)

theorem e6_beta_char_contraction_iff (c : ℕ) (hc : 1 ≤ c) :
    |e6BetaConjChar c| < 1 ↔ c = 1 := by
  rw [e6_beta_char_abs c]
  constructor
  · intro hcontraction
    have hbeta_lt_two : e6Beta c < 2 := by linarith
    have hpositive : 0 < (2 - e6Beta c) * (e6Beta c + 1) := by
      exact mul_pos (by linarith) (by nlinarith [e6_beta_ge_one c])
    have hc_lt_two_real : (c : ℝ) < 2 := by
      nlinarith [e6_beta_sq c]
    have hc_lt_two : c < 2 := by exact_mod_cast hc_lt_two_real
    omega
  · rintro rfl
    rw [e6_beta_one, Real.goldenRatio]
    have hsqrt_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith

@[simp] theorem e6_beta_char_abs_two : |e6BetaConjChar 2| = 1 := by
  norm_num [e6BetaConjChar]

/-- Strict escape: for `c ≥ 3` the companion root lies strictly outside the
closed unit disc, completing the trichotomy with `e6_beta_char_contraction_iff`
(`c = 1` strictly inside) and `e6_beta_char_abs_two` (`c = 2` on the circle). -/
theorem e6_beta_char_abs_gt_one (c : ℕ) (hc : 3 ≤ c) :
    1 < |e6BetaConjChar c| := by
  have hc_real : (3 : ℝ) ≤ c := by exact_mod_cast hc
  have hgt : 2 < e6Beta c := by
    nlinarith [e6_beta_sq c, e6_beta_ge_one c]
  rw [e6_beta_char_abs c]
  linarith

theorem e6_beta_char_abs_pronic (m : ℕ) :
    |e6BetaConjChar (m * (m + 1))| = m := by
  have hbeta : e6Beta (m * (m + 1)) = (m : ℝ) + 1 := by
    symm
    apply e6_beta_unique
    · positivity
    · push_cast
      ring
  rw [e6BetaConjChar, hbeta]
  norm_num

end D5.S1.Digit
