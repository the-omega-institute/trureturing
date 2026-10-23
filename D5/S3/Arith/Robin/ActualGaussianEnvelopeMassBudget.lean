/- SOURCE ONLY. Complete spectral response and direct inverse-square bound.
   The norm of the signed integral is bounded; no pointwise smallness of
   the absolute-value integrand is asserted. -/
import D5.S3.Weil.ZeroData.ActualGaussianMass
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZeroData.ActualGaussianMass
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange

namespace D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget

private def response (m γ : ℝ) (k : ℕ) : ℂ :=
  (1 / (actualZero k * (1 - actualZero k))) *
    (2 * (actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))) *
      Complex.exp ((m : ℂ) * actualZero k ^ 2 + 16 * (m : ℂ) * actualZero k))

private theorem height_suppression (t γ m : ℝ) (ht : 100 ≤ t ^ 2)
    (hγ : 10 < γ) (hm : 1 ≤ m) :
    (t ^ 2 + γ ^ 2 + 5 / 2) * Real.exp (-m * t ^ 2) ≤
      (γ + 10) ^ 2 * Real.exp (-100 * m) := by
  let u := t ^ 2 - 100
  let A := γ ^ 2 + 205 / 2
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg γ]
  have hD : A ≤ (γ + 10) ^ 2 := by dsimp [A]; nlinarith
  have hlin : A + u ≤ A * Real.exp (m * u) := by
    have h1 : A + u ≤ A * (1 + u) := by nlinarith
    have h2 : 1 + u ≤ Real.exp (m * u) := by
      linarith [Real.add_one_le_exp (m * u),
        mul_le_mul_of_nonneg_right hm hu]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  have he : Real.exp (m * u) * Real.exp (-m * t ^ 2) =
      Real.exp (-100 * m) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  calc
    _ = (A + u) * Real.exp (-m * t ^ 2) := by dsimp [A, u]; ring
    _ ≤ (A * Real.exp (m * u)) * Real.exp (-m * t ^ 2) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
    _ = A * Real.exp (-100 * m) := by rw [mul_assoc, he]
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)

private theorem response_polynomial_bound (m γ : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    ‖actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1 + 1 / (2 * (m : ℂ))‖ ≤
      (actualZero k).im ^ 2 + γ ^ 2 + 5 / 2 := by
  have hmpos : 0 < m := by linarith
  have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  have hs' : 0 < (actualZero k).re ∧ (actualZero k).re < 1 := by
    simpa only [actualZero] using hs
  have hr : (actualZero k).re ^ 2 ≤ 1 := by nlinarith
  have hn : ‖actualZero k‖ ^ 2 = (actualZero k).re ^ 2 + (actualZero k).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hγ : ‖(γ : ℂ) ^ 2‖ = γ ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hhalf : ‖(1 / (2 * (m : ℂ)) : ℂ)‖ ≤ (1 : ℝ) / 2 := by
    have he : ‖(1 / (2 * (m : ℂ)) : ℂ)‖ = 1 / (2 * m) := by
      simp only [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmpos]
    rw [he]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m) (by norm_num)).2
    nlinarith
  calc
    _ ≤ ‖actualZero k ^ 2 + (γ : ℂ) ^ 2 + 1‖ + ‖(1 / (2 * (m : ℂ)) : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ (‖actualZero k ^ 2‖ + ‖(γ : ℂ) ^ 2‖ + ‖(1 : ℂ)‖) +
        ‖(1 / (2 * (m : ℂ)) : ℂ)‖ := by
      gcongr
      exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by rw [norm_pow, hγ, norm_one, hn]; linarith

private theorem response_exp_bound (m : ℝ) (hm : 1 ≤ m) (k : ℕ) :
    ‖Complex.exp ((m : ℂ) * actualZero k ^ 2 + 16 * (m : ℂ) * actualZero k)‖ ≤
      Real.exp (17 * m) * Real.exp (-m * (actualZero k).im ^ 2) := by
  have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
  have hs' : 0 < (actualZero k).re ∧ (actualZero k).re < 1 := by
    simpa only [actualZero] using hs
  have hb : (actualZero k).re ^ 2 + 16 * (actualZero k).re ≤ 17 := by
    nlinarith [mul_nonneg hs'.1.le (sub_nonneg.mpr hs'.2.le)]
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  nlinarith

private theorem response_norm_bound (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) (k : ℕ) :
    ‖response m γ k‖ ≤
      (2 * (γ + 10) ^ 2 * Real.exp (-83 * m)) * ((actualZero k).im)⁻¹ ^ 2 := by
  have ht : 100 ≤ (actualZero k).im ^ 2 := by
    nlinarith [occurrence_height k, sq_abs (actualZero k).im]
  have hp := response_polynomial_bound m γ hm k
  have hc := coefficient_norm_le k
  have he := response_exp_bound m hm k
  have hs := height_suppression (actualZero k).im γ m ht hγ hm
  have hnorm : ‖response m γ k‖ ≤ ((actualZero k).im)⁻¹ ^ 2 *
      (2 * ((actualZero k).im ^ 2 + γ ^ 2 + 5 / 2) *
        (Real.exp (17 * m) * Real.exp (-m * (actualZero k).im ^ 2))) := by
    dsimp [response]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    exact mul_le_mul hc (mul_le_mul
      (mul_le_mul_of_nonneg_left hp (by norm_num)) he
      (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
  calc
    _ ≤ ((actualZero k).im)⁻¹ ^ 2 * (2 * Real.exp (17 * m) *
        (((actualZero k).im ^ 2 + γ ^ 2 + 5 / 2) *
          Real.exp (-m * (actualZero k).im ^ 2))) := by nlinarith [hnorm]
    _ ≤ ((actualZero k).im)⁻¹ ^ 2 *
        (2 * Real.exp (17 * m) * ((γ + 10) ^ 2 * Real.exp (-100 * m))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs
          (by positivity : 0 ≤ 2 * Real.exp (17 * m)))
        (sq_nonneg ((actualZero k).im)⁻¹)
    _ = _ := by
      have heq : Real.exp (17 * m) * Real.exp (-100 * m) = Real.exp (-83 * m) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (2 * (γ + 10) ^ 2 * (Real.exp (17 * m) * Real.exp (-100 * m))) *
            ((actualZero k).im)⁻¹ ^ 2 := by ring
        _ = _ := by rw [heq]

/-- The whole complex response is absolutely convergent by the actual mass. -/
private theorem response_summable (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    Summable (response m γ) :=
  Summable.of_norm_bounded
    (inverse_square_summable.mul_left (2 * (γ + 10) ^ 2 * Real.exp (-83 * m)))
    (response_norm_bound m γ hm hγ)

/-- Strong direct-mass response. Integrability and the full actual spectral
exchange come from the complete repaired source, not from a budget premise. -/
theorem full_Hv_le_four (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    |∫ y : ℝ, (H y).re * gaussianV m γ y| ≤
      4 * (γ + 10) ^ 2 * Real.exp (-83 * m) := by
  have hmpos : 0 < m := by linarith
  have hp := H_weighted_V_product_integrable m γ hmpos
  have hex : HasSum (response m γ)
      (∫ y : ℝ, H y * (gaussianV m γ y : ℂ)) := by
    convert actual_signed_V_exchange m γ hmpos using 1
    funext k
    dsimp [response]
  have hre : (∫ y : ℝ, H y * (gaussianV m γ y : ℂ)).re =
      ∫ y : ℝ, (H y).re * gaussianV m γ y := by
    calc
      _ = ∫ y : ℝ, (H y * (gaussianV m γ y : ℂ)).re :=
        (integral_re hp).symm
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all volume fun y => by simp only [Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hs := (inverse_square_summable.mul_left
    (2 * (γ + 10) ^ 2 * Real.exp (-83 * m))).hasSum
  have habs := (response_summable m γ hm hγ).norm
  calc
    _ = |(∫ y : ℝ, H y * (gaussianV m γ y : ℂ)).re| := congrArg abs hre.symm
    _ ≤ ‖∫ y : ℝ, H y * (gaussianV m γ y : ℂ)‖ := Complex.abs_re_le_norm _
    _ = ‖∑' k, response m γ k‖ := by rw [hex.tsum_eq]
    _ ≤ ∑' k : ℕ, ‖response m γ k‖ := norm_tsum_le_tsum_norm habs
    _ ≤ (2 * (γ + 10) ^ 2 * Real.exp (-83 * m)) *
        (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) := by
      simpa only [tsum_mul_left] using
        habs.tsum_le_tsum (response_norm_bound m γ hm hγ) hs.summable
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left mass_lt_two.le
        (by positivity : 0 ≤ 2 * (γ + 10) ^ 2 * Real.exp (-83 * m))
      nlinarith

theorem full_Hv_original (m γ : ℝ) (hm : 1 ≤ m) (hγ : 10 < γ) :
    |∫ y : ℝ, (H y).re * gaussianV m γ y| ≤
      1000 * (γ + 10) ^ 2 * Real.exp (-83 * m) := by
  exact (full_Hv_le_four m γ hm hγ).trans (by
    nlinarith [mul_nonneg (sq_nonneg (γ + 10)) (Real.exp_nonneg (-83 * m))])

end D5.S3.Arith.Robin.ActualGaussianEnvelopeMassBudget
