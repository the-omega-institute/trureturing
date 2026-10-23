/- SOURCE CANDIDATE ONLY. Absolute convergence of the COMPLETE E_gamma,
   with no reciprocal weights in E itself. The majorant uses the previously
   proved actual inverse-square mass. Sharp tail constants and the original
   finite Cassel time are implemented in ActualGaussianDirectTail. -/
import D5.S3.Weil.ZeroData.ActualGaussianMass
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZeroData.ActualGaussianZeroSum
open scoped BigOperators
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualGaussianMass

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
