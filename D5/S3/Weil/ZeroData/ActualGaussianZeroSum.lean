/- GID: D5/S3/Weil/ZeroData/ActualGaussianZeroSum
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ActualGaussianZeroSum
   mirror-E: none(waiver:analytic-proof-without-numeric-projection)
   anchors: []
   utility: none
   digest: Quantitative complete Gaussian localization for the original positive-U theorem. -/
/- SOURCE CANDIDATE ONLY. Absolute convergence of the COMPLETE E_gamma,
   with no reciprocal weights in E itself. The majorant uses the previously
   proved actual inverse-square mass. Sharp tail constants and the original
   finite Cassel time are implemented in ActualGaussianDirectTail. -/
import D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZeroData.ActualGaussianZeroSum
open scoped BigOperators
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
open MeasureTheory

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

def summand (m γ : ℝ) (rho : ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * ((rho - Complex.I * (γ : ℂ)) ^ 2 +
    16 * (rho - Complex.I * (γ : ℂ))))

def E (m γ : ℝ) : ℂ := ∑' k : ℕ, summand m γ (actualZero k)

private theorem shifted_gaussian_domination (η γ m : ℝ) (hη : η ≠ 0) (hm : 1 ≤ m) :
    Real.exp (-m * (η - γ) ^ 2) ≤ (2 + 2 * γ ^ 2) * η⁻¹ ^ 2 := by
  have ht : (η - γ) ^ 2 ≤ Real.exp (m * (η - γ) ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right hm (sq_nonneg (η - γ))
    linarith [Real.add_one_le_exp (m * (η - γ) ^ 2)]
  have hp := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg (-m * (η - γ) ^ 2))
  have heq : Real.exp (m * (η - γ) ^ 2) * Real.exp (-m * (η - γ) ^ 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [heq] at hp
  have he : Real.exp (-m * (η - γ) ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg (η - γ)]
  have htri : η ^ 2 ≤ 2 * (η - γ) ^ 2 + 2 * γ ^ 2 := by
    nlinarith [sq_nonneg (η - 2 * γ)]
  have hscaled := mul_le_mul_of_nonneg_right htri
    (Real.exp_nonneg (-m * (η - γ) ^ 2))
  have hγ := mul_le_mul_of_nonneg_left he (sq_nonneg γ)
  have hlast : Real.exp (-m * (η - γ) ^ 2) * η ^ 2 ≤ 2 + 2 * γ ^ 2 := by
    nlinarith
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (sq_pos_of_ne_zero hη)]
  exact hlast

/-- The all-zero Gaussian summand admits an absolute inverse-square majorant. -/
theorem summand_norm_le (m γ : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    ‖summand m γ (actualZero k)‖ ≤
      (Real.exp (17 * m) * (2 + 2 * γ ^ 2)) * ((actualZero k).im)⁻¹ ^ 2 := by
  let rho := actualZero k
  have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  have hs' : 0 < rho.re ∧ rho.re < 1 := by
    simpa only [rho, actualZero] using hs
  have hη : rho.im ≠ 0 := by
    have hh := actual_height_gt_ten rho
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    intro he
    rw [he, abs_zero] at hh
    linarith
  have hre : rho.re ^ 2 + 16 * rho.re ≤ 17 := by
    nlinarith [mul_nonneg hs'.1.le (sub_nonneg.mpr hs'.2.le)]
  have hnorm : ‖summand m γ rho‖ =
      Real.exp (m * (rho.re ^ 2 + 16 * rho.re - (rho.im - γ) ^ 2)) := by
    rw [summand, Complex.norm_exp]
    congr 1
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hnorm]
  calc
    _ ≤ Real.exp (17 * m + (-m * (rho.im - γ) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (17 * m) * Real.exp (-m * (rho.im - γ) ^ 2) := Real.exp_add _ _
    _ ≤ Real.exp (17 * m) * ((2 + 2 * γ ^ 2) * rho.im⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left (shifted_gaussian_domination _ _ _ hη hm)
        (Real.exp_nonneg _)
    _ = _ := by ring

/-- E is a genuine absolutely convergent full zero sum for all original times. -/
theorem E_summable (m γ : ℝ) (hm : 1 ≤ m) :
    Summable (fun k : ℕ => summand m γ (actualZero k)) := by
  apply summable_norm_iff.mp
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (summand_norm_le m γ hm) (inverse_square_summable.mul_left _)

end D5.S3.Weil.ZeroData.ActualGaussianZeroSum
