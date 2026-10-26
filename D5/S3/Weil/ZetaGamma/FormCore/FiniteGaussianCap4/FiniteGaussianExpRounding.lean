/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianExpRounding
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Rational exponential endpoints for the finite Gaussian cap certificate. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianAnalyticEndpoints

/-! Exact rational exponential endpoints, checked from the analytic Taylor bounds.
The integers come from the original outward-rounded certificate. Their values
are mathematical data and all comparisons are proved by ordinary norm_num.
This is a consumed-helper source for the signed compact multiplier certificate;
it does not assert the whole certificate or any RH implication.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
noncomputable section
open Finset

namespace RHFiniteGaussian.AnalyticEndpoints

def expNeg12Lower250 : ℚ := 61442123533282097586823081788055323112239893148882529755685058764998835778094886157674236584082278705983104644228305160477255947038660886572527460818482959256755886760922090885775024673941310925186631379436377864504929642521934868138634717794433 / (10 : ℚ) ^ 250
def expNeg12Upper250 : ℚ := 61442123533282097586823081788055323112239893148882529755685058764998835778094886157674236584082278705983104644228305160477255947038660886572527460818482959256755886760922090885775024673941310925186631379436377864504929642521934868138634717794435 / (10 : ℚ) ^ 250

set_option exponentiation.threshold 1024 in
/-- Actual endpoint comparison for the original 250-place exponential box. -/
theorem exp_neg_twelve_rounding_comparisons :
    expNeg12Lower250 ≤ expNeg12LowerQ ∧ expNeg12UpperQ ≤ expNeg12Upper250 := by
  norm_num [expNeg12Lower250, expNeg12Upper250, expNeg12LowerQ,
    expNeg12UpperQ, expUpperQ, expPrefixQ, Finset.sum_range_succ]

/-- The completed certificate's concrete outward-rounded exp(-12) input. -/
theorem exp_neg_twelve_250_bounds :
    (expNeg12Lower250 : ℝ) ≤ Real.exp (-12) ∧
      Real.exp (-12) ≤ (expNeg12Upper250 : ℝ) := by
  have hl : (expNeg12Lower250 : ℝ) ≤ (expNeg12LowerQ : ℝ) := by
    exact_mod_cast exp_neg_twelve_rounding_comparisons.1
  have hu : (expNeg12UpperQ : ℝ) ≤ (expNeg12Upper250 : ℝ) := by
    exact_mod_cast exp_neg_twelve_rounding_comparisons.2
  exact ⟨hl.trans exp_neg_twelve_bounds.1, exp_neg_twelve_bounds.2.trans hu⟩

/-- Range reduction uses the already-proved 250-place pi box, avoiding the
large exact Machin denominator in the subsequent Taylor evaluation. -/
def expNegTwoPiRoundedLowerQ : ℚ := 1 / expUpperQ (piUpper250 / 8) 240 ^ 16
def expNegTwoPiRoundedUpperQ : ℚ := 1 / expPrefixQ (piLower250 / 8) 240 ^ 16

theorem exp_neg_two_pi_rounded_bounds :
    (expNegTwoPiRoundedLowerQ : ℝ) ≤ Real.exp (-(2 * Real.pi)) ∧
      Real.exp (-(2 * Real.pi)) ≤ (expNegTwoPiRoundedUpperQ : ℝ) := by
  have hylo0 : (0 : ℝ) ≤ (piLower250 : ℝ) / 8 := by
    norm_num [piLower250]
  have hylo1 : (piLower250 : ℝ) / 8 < 1 := by
    norm_num [piLower250]
  have hyhi0 : (0 : ℝ) ≤ (piUpper250 : ℝ) / 8 := by
    norm_num [piUpper250]
  have hyhi1 : (piUpper250 : ℝ) / 8 < 1 := by
    norm_num [piUpper250]
  have hlo := exp_neg_sixteen_bounds hylo0 hylo1 240
  have hhi := exp_neg_sixteen_bounds hyhi0 hyhi1 240
  have helo : Real.exp (-(16 * ((piUpper250 : ℝ) / 8))) ≤ Real.exp (-(2 * Real.pi)) :=
    Real.exp_le_exp.mpr (by
      convert neg_le_neg (mul_le_mul_of_nonneg_left pi_250_bounds.2 (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;> ring)
  have hehi : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-(16 * ((piLower250 : ℝ) / 8))) :=
    Real.exp_le_exp.mpr (by
      convert neg_le_neg (mul_le_mul_of_nonneg_left pi_250_bounds.1 (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;> ring)
  constructor
  · simpa [expNegTwoPiRoundedLowerQ] using hhi.1.trans helo
  · simpa [expNegTwoPiRoundedUpperQ] using hehi.trans hlo.2

end RHFiniteGaussian.AnalyticEndpoints
