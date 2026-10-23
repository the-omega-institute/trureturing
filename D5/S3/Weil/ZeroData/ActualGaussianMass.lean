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
  have hs : Summable (fun p : ActualZeroOccurrence =>
      ((actualData.zero p.1).im)⁻¹ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using actual_weighted_inverse_square_summable
  simpa only [Function.comp_def, actualZero] using
    (actualOccurrenceEquiv.summable_iff).2 hs

/- The following body is reused from the private pinned actual63 proof.
   It is proved here, rather than referring to an inaccessible declaration. -/
private theorem li_mass_lt_one : firstLiMass < 1 := by
  have hg : Real.eulerMascheroniConstant < 1 :=
    Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  have hroot : 3 < 2 * Real.sqrt Real.pi := by
    by_contra h
    have hle : 2 * Real.sqrt Real.pi ≤ 3 := le_of_not_gt h
    have hprod : 0 ≤ (3 / 2 - Real.sqrt Real.pi) *
        (3 / 2 + Real.sqrt Real.pi) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.pi_gt_three]
  have hlog : 1 < Real.log (2 * Real.sqrt Real.pi) :=
    (Real.lt_log_iff_exp_lt (by positivity)).2 (Real.exp_one_lt_three.trans hroot)
  unfold firstLiMass
  linarith

theorem mass_lt_two : (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) < 2 := by
  have hs : (101 / 100 : ℝ) * firstLiMass < 2 := by
    linarith [li_mass_lt_one]
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
  have hdom (k : ℕ) :
      ‖(1 / (actualZero k * (1 - actualZero k))) *
        Complex.exp ((y : ℂ) * actualZero k)‖ ≤
        ((actualZero k).im)⁻¹ ^ 2 * Real.exp (max y 0) := by
    have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
    have hexp : y * (actualZero k).re ≤ max y 0 := by
      rcases le_or_gt 0 y with hy | hy
      · rw [max_eq_left hy]
        simpa only [actualZero, mul_one] using mul_le_mul_of_nonneg_left hs.2.le hy
      · rw [max_eq_right hy.le]
        exact mul_nonpos_of_nonpos_of_nonneg hy.le hs.1.le
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_le_mul (coefficient_norm_le k) (Real.exp_le_exp.mpr hexp)
      (Real.exp_nonneg _) (sq_nonneg _)
  have hmajor : HasSum
      (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2 * Real.exp (max y 0))
      ((∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0)) :=
    inverse_square_summable.hasSum.mul_right _
  have hbound : ‖H y‖ ≤
      (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0) := by
    exact tsum_of_norm_bounded hmajor hdom
  exact hbound.trans (mul_le_mul_of_nonneg_right mass_lt_two.le (Real.exp_nonneg _))

theorem H_re_abs_le (y : ℝ) : |(H y).re| ≤ 2 * Real.exp (max y 0) :=
  (Complex.abs_re_le_norm _).trans (H_norm_le y)

end D5.S3.Weil.ZeroData.ActualGaussianMass
