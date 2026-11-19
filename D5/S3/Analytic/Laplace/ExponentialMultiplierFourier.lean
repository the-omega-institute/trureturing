/- GID: D5/S3/Analytic/Laplace/ExponentialMultiplierFourier
   generality: I
   mirror-B: D5/B/S3/Analytic/Laplace/ExponentialMultiplierFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential smoothing contracts the raw inverse Fourier transform in L². -/

import D5.S3.Analytic.Laplace.ExponentialMultiplierContour
import D5.S3.Weil.ZetaGamma.FormCore.LineFourier

/-! The exponential multiplier in Mathlib's normalized inverse Fourier convention. -/

namespace D5.S3.Analytic.Laplace.ExponentialMultiplierContour

open Complex MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The target-line multiplier, with angular frequency `2 * π * ξ`. -/
def targetMultiplier (c ξ : ℝ) : ℂ :=
  (c : ℂ) / ((c : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)

private theorem norm_targetMultiplier_le_one {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    ‖targetMultiplier c ξ‖ ≤ 1 := by
  have h : c ≤ ‖(c : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I‖ := by
    simpa using Complex.re_le_norm ((c : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)
  rw [targetMultiplier, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  exact (div_le_iff₀ (hc.trans_le h)).2 (by simpa using h)

set_option maxHeartbeats 600000 in
-- Comparing the function and Lp Fourier instances requires extra elaboration.
/-- For an L² frequency section whose smoothed section is integrable, the
pointwise inverse Fourier integral is in L² with norm at most the original one. -/
theorem targetInverse_memLp {c : ℝ} (hc : 0 < c) {f : ℝ → ℂ} (hf : MemLp f 2)
    (h₁ : Integrable (fun ξ => f ξ * targetMultiplier c ξ)) :
    MemLp (𝓕⁻ (fun ξ => f ξ * targetMultiplier c ξ)) 2 ∧
      eLpNorm (𝓕⁻ (fun ξ => f ξ * targetMultiplier c ξ)) 2 ≤ eLpNorm f 2 := by
  let g : ℝ → ℂ := fun ξ => f ξ * targetMultiplier c ξ
  have hle (ξ : ℝ) : ‖g ξ‖ ≤ ‖f ξ‖ := by
    change ‖f ξ * targetMultiplier c ξ‖ ≤ ‖f ξ‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_targetMultiplier_le_one hc ξ)
  have h₁g : Integrable g := h₁
  have h₂ : MemLp g 2 := hf.mono h₁g.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  let G : Lp ℂ 2 volume := 𝓕 (h₂.toLp g)
  have hae : (𝓕 g : ℝ → ℂ) =ᵐ[volume] G :=
    D5.S3.Weil.ZetaGamma.FormCore.LineFourier.raw_fourier_ae_eq_L2 h₁g h₂
  have hraw : MemLp (𝓕 g) 2 := MemLp.ae_eq hae.symm (Lp.memLp G)
  have hflip : 𝓕⁻ g = (𝓕 g) ∘ (fun x : ℝ => -x) := by
    funext x
    exact Real.fourierInv_eq_fourier_neg g x
  have hpres := Measure.measurePreserving_neg (volume : Measure ℝ)
  change MemLp (𝓕⁻ g) 2 ∧ eLpNorm (𝓕⁻ g) 2 ≤ eLpNorm f 2
  rw [hflip]
  refine ⟨hraw.comp_measurePreserving hpres, ?_⟩
  rw [eLpNorm_comp_measurePreserving hraw.aestronglyMeasurable hpres]
  exact (D5.S3.Weil.ZetaGamma.FormCore.LineFourier.raw_fourier_eLpNorm_eq h₁g h₂).le.trans
    (eLpNorm_mono h₁g.aestronglyMeasurable hle)

/-- The normalized raw inverse integral is the target-line integral divided by `2 * π`. -/
theorem targetInverse_eq_vertical_integral (σ c t : ℝ) (F : ℂ → ℂ) :
    𝓕⁻ (fun ξ : ℝ => F ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) *
      targetMultiplier c ξ) t =
      (2 * Real.pi)⁻¹ • ∫ y : ℝ, smoothed σ c t F ((σ : ℂ) + y * I) := by
  rw [Real.fourierInv_eq']
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [← abs_of_pos (inv_pos.mpr hπ), ← Measure.integral_comp_mul_left]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [smoothed, targetMultiplier, Real.inner_apply, smul_eq_mul]
  have hphase :
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I - σ) * (t : ℂ) =
        ((2 * (Real.pi * (ξ * t)) : ℝ) : ℂ) * I := by push_cast; ring
  have hden : (c : ℂ) + ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) - σ =
      (c : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by ring
  rw [hphase, hden]
  simp only [mul_assoc]

end

end D5.S3.Analytic.Laplace.ExponentialMultiplierContour
