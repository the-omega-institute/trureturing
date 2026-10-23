/- SOURCE ONLY. Restricted integrals are obtained by dominated convergence
   directly on the exact restricted measure, with full inverse-square L1
   domination paid. No half-axis integral is identified with the whole
   Gaussian transform; no private occurrence-package API is imported. -/
import D5.S3.Weil.ZeroData.ActualGaussianMass
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Arith.Robin.CompleteActualSignedGaussianExchange
open D5.S3.Weil.ZeroData.ActualGaussianMass

namespace D5.S3.Arith.Robin.ActualGaussianRestrictedExchange

private theorem restricted_exchange (s : Set ℝ) (hs : MeasurableSet s)
    (w : ℝ → ℂ) (hw : Continuous w)
    (hwi : Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖)) :
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      ∫ y in s, Complex.exp ((y : ℂ) * actualZero k) * w y)
      (∫ y in s, H y * w y) := by
  let a : ℕ → ℂ := fun k => 1 / (actualZero k * (1 - actualZero k))
  let F : ℕ → ℝ → ℂ := fun k y =>
    a k * Complex.exp ((y : ℂ) * actualZero k) * w y
  let B : ℕ → ℝ → ℝ := fun k y =>
    ((actualZero k).im)⁻¹ ^ 2 * (Real.exp (max y 0) * ‖w y‖)
  have hFcont (k : ℕ) : Continuous (F k) := by
    dsimp [F]
    exact (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))).mul hw
  have hdom (k : ℕ) (y : ℝ) : ‖F k y‖ ≤ B k y := by
    have hz := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
    have he : y * (actualZero k).re ≤ max y 0 := by
      rcases le_or_gt 0 y with hy | hy
      · rw [max_eq_left hy]
        simpa only [actualZero, mul_one] using mul_le_mul_of_nonneg_left hz.2.le hy
      · rw [max_eq_right hy.le]
        exact mul_nonpos_of_nonpos_of_nonneg hy.le hz.1.le
    dsimp [F, a, B]
    rw [norm_mul, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    calc
      _ ≤ (((actualZero k).im)⁻¹ ^ 2 * Real.exp (max y 0)) * ‖w y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (coefficient_norm_le k) (Real.exp_le_exp.mpr he)
            (Real.exp_nonneg _) (sq_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hsum (y : ℝ) : Summable (fun k : ℕ => F k y) :=
    Summable.of_norm_bounded
      (inverse_square_summable.mul_right (Real.exp (max y 0) * ‖w y‖))
      (fun k => hdom k y)
  have hBsum : ∀ᵐ y ∂volume.restrict s, Summable (fun k => B k y) :=
    ae_of_all _ fun y =>
      inverse_square_summable.mul_right (Real.exp (max y 0) * ‖w y‖)
  have hBI : Integrable (fun y => ∑' k, B k y) (volume.restrict s) := by
    change IntegrableOn (fun y => ∑' k, B k y) s volume
    simpa only [B, tsum_mul_right] using
      (hwi.const_mul (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2)).integrableOn
  have hlim : ∀ᵐ y ∂volume.restrict s,
      HasSum (fun k => F k y) (H y * w y) := by
    exact ae_of_all _ fun y => by
      simpa only [F, a, H, tsum_mul_right] using (hsum y).hasSum
  have hresult := hasSum_integral_of_dominated_convergence B
    (fun k => (hFcont k).aestronglyMeasurable)
    (fun k => ae_of_all _ fun y => hdom k y) hBsum hBI hlim
  convert hresult using 1
  funext k
  simpa only [F, a, integral_const_mul, mul_assoc]

/-- Every measurable restriction, including either axis and either exterior,
retains the entire actual occurrence family and paid ordinary integrability. -/
theorem V_exchange_on (s : Set ℝ) (hs : MeasurableSet s)
    (m γ : ℝ) (hm : 0 < m) :
    IntegrableOn (fun y : ℝ => H y * (gaussianV m γ y : ℂ)) s ∧
    (∀ k : ℕ, IntegrableOn (fun y : ℝ =>
      Complex.exp ((y : ℂ) * actualZero k) * (gaussianV m γ y : ℂ)) s) ∧
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      ∫ y in s, Complex.exp ((y : ℂ) * actualZero k) * (gaussianV m γ y : ℂ))
      (∫ y in s, H y * (gaussianV m γ y : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (gaussianV m γ y : ℂ)) := by
    unfold gaussianV gaussianU gaussianDensity
    fun_prop
  refine ⟨(H_weighted_V_product_integrable m γ hm).integrableOn, ?_,
    restricted_exchange s hs _ hc
      (gaussianV_weighted_integrable m γ hm)⟩
  intro k
  have ht := gaussianV_tilt_integrable m γ hm (actualZero k)
  have he : (fun y : ℝ => Complex.exp ((y : ℂ) * actualZero k) *
      (gaussianV m γ y : ℂ)) =
      (fun y : ℝ => Complex.exp (actualZero k * (y : ℂ)) *
        (gaussianV m γ y : ℂ)) := by funext y; rw [mul_comm (y : ℂ)]
  rw [he]
  exact ht.integrableOn

theorem W_exchange_on (s : Set ℝ) (hs : MeasurableSet s)
    (m γ : ℝ) (hm : 0 < m) :
    IntegrableOn (fun y : ℝ => H y * gaussianW m γ y) s ∧
    (∀ k : ℕ, IntegrableOn (fun y : ℝ =>
      Complex.exp ((y : ℂ) * actualZero k) * gaussianW m γ y) s) ∧
    HasSum (fun k : ℕ => (1 / (actualZero k * (1 - actualZero k))) *
      ∫ y in s, Complex.exp ((y : ℂ) * actualZero k) * gaussianW m γ y)
      (∫ y in s, H y * gaussianW m γ y) := by
  have hc : Continuous (gaussianW m γ) := by
    unfold gaussianW gaussianP gaussianU gaussianDensity
    fun_prop
  refine ⟨(H_weighted_product_integrable m γ hm).integrableOn, ?_,
    restricted_exchange s hs _ hc
      (gaussianW_weighted_integrable m γ hm)⟩
  intro k
  have ht := gaussianW_tilt_integrable m γ hm (actualZero k)
  have he : (fun y : ℝ => Complex.exp ((y : ℂ) * actualZero k) * gaussianW m γ y) =
      (fun y : ℝ => Complex.exp (actualZero k * (y : ℂ)) * gaussianW m γ y) := by
    funext y
    rw [mul_comm (y : ℂ)]
  rw [he]
  exact ht.integrableOn

end D5.S3.Arith.Robin.ActualGaussianRestrictedExchange
