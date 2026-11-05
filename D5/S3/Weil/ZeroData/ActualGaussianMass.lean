/- GID: D5/S3/Weil/ZeroData/ActualGaussianMass
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ActualGaussianMass
   mirror-E: none(waiver:analytic-proof-without-numeric-projection)
   anchors: []
   utility: none
   digest: Quantitative complete Gaussian localization for the original positive-U theorem. -/
/- SOURCE IMPLEMENTATION ONLY; not elaborated. All occurrences, both signs,
   and exact analytic multiplicities are those of the pinned actualData. -/
import D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange

namespace D5.S3.Weil.ZeroData.ActualGaussianMass

/-- Finite multiplicity fibers and the actual natural equivalence pay the
summability transport; no noncanonical enumeration or missing sign is used. -/
theorem inverse_square_summable :
    Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
  simpa only [Function.comp_def, actualZero] using
    (actualOccurrenceEquiv.summable_iff).2 actual_sigma_inverse_square_summable

theorem mass_lt_two : (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) < 2 := by
  have hs : (101 / 100 : ℝ) * firstLiMass < 2 := by
    linarith [firstLiMass_lt_one]
  exact actual_inverse_square_mass_le_height.trans_lt hs

theorem occurrence_height (k : ℕ) : 10 < |(actualZero k).im| :=
  actual_height_gt_ten _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)

theorem coefficient_norm_le (k : ℕ) :
    ‖(1 / (actualZero k * (1 - actualZero k)) : ℂ)‖ ≤
      ((actualZero k).im)⁻¹ ^ 2 := by
  have ht : 0 < (actualZero k).im ^ 2 := by
    nlinarith [occurrence_height k, sq_abs (actualZero k).im]
  have h1 := Complex.abs_im_le_norm (actualZero k)
  have h2 : |(actualZero k).im| ≤ ‖1 - actualZero k‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm (1 - actualZero k)
  have hd : (actualZero k).im ^ 2 ≤ ‖actualZero k‖ * ‖1 - actualZero k‖ := by
    simpa only [← pow_two, sq_abs] using
      mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  rw [norm_div, norm_one, norm_mul]
  calc
    _ ≤ 1 / ((actualZero k).im ^ 2) := one_div_le_one_div_of_le ht hd
    _ = _ := by rw [one_div, inv_pow]

/-- Growth of the consumed complex H; this does not introduce another H. -/
theorem H_norm_le (y : ℝ) : ‖H y‖ ≤ 2 * Real.exp (max y 0) := by
  have hb : ‖H y‖ ≤ ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0) := by
    simpa only [H, D5.S3.Weil.Mertens.IntegratedExplicit.actualH,
      D5.S3.Weil.Mertens.IntegratedExplicit.actualCoeff] using
      D5.S3.Weil.Mertens.IntegratedExplicit.actualH_bound y
  exact hb.trans (mul_le_mul_of_nonneg_right
    (by linarith [firstLiMass_lt_one] : (101 / 100 : ℝ) * firstLiMass ≤ 2)
    (Real.exp_nonneg _))

theorem H_re_abs_le (y : ℝ) : |(H y).re| ≤ 2 * Real.exp (max y 0) :=
  (Complex.abs_re_le_norm _).trans (H_norm_le y)

end D5.S3.Weil.ZeroData.ActualGaussianMass
