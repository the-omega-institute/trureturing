/- GID: D5/S3/Analytic/Fourier/RawFourierL2
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/RawFourierL2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The integral and L² Fourier transforms agree on integrable square-integrable functions. -/

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Tactic.NormNum

/-! Compatibility of the integral and L² Fourier transforms on the real line. -/

namespace D5.S3.Analytic.Fourier.RawFourierL2

open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap

private theorem raw_fourier_test {f : ℝ → ℂ} (hf : Integrable f)
    (ψ : SchwartzMap ℝ ℂ) :
    (∫ ξ : ℝ, ψ ξ • 𝓕 f ξ) = ∫ x : ℝ, 𝓕 ψ x • f x := by
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral,
    Real.inner_apply, smul_eq_mul, mul_comm] using!
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (f := f) (g := (ψ : ℝ → ℂ)) (.mul ℂ ℂ) (L := innerₗ ℝ)
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Real.continuous_fourierChar continuous_inner hf (ψ.integrable (μ := volume))

/-- The integral Fourier transform agrees almost everywhere with the `L²` transform. -/
theorem raw_fourier_ae_eq_L2 {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    (𝓕 f : ℝ → ℂ) =ᵐ[volume]
      (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) := by
  let F : Lp ℂ 2 volume := 𝓕 (hf₂.toLp f)
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf₁
  apply ae_eq_of_integral_contDiff_smul_eq
    hcont.locallyIntegrable
    ((Lp.memLp F).locallyIntegrable (by norm_num))
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Complex.ofRealCLM ∘ g) :=
    Complex.ofRealCLM.contDiff.comp hg
  let ψ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂
  have hdist := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ)
    (Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    (∫ ξ : ℝ, g ξ • 𝓕 f ξ) = ∫ ξ : ℝ, ψ ξ • 𝓕 f ξ := by
      simp [ψ, Function.comp_apply]
    _ = ∫ x : ℝ, 𝓕 ψ x • f x := raw_fourier_test hf₁ ψ
    _ = ∫ x : ℝ, 𝓕 ψ x • (hf₂.toLp f) x := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ ξ : ℝ, ψ ξ • F ξ := hdist
    _ = ∫ ξ : ℝ, g ξ • F ξ := by
      simp [ψ, Function.comp_apply]

/-- The integral Fourier transform preserves the `L²` seminorm on `L¹ ∩ L²`. -/
theorem raw_fourier_eLpNorm_eq {f : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  calc
    _ = eLpNorm (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) 2 volume :=
      eLpNorm_congr_ae (raw_fourier_ae_eq_L2 hf₁ hf₂)
    _ = ‖𝓕 (hf₂.toLp f)‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hf₂.toLp f‖ₑ := (Lp.fourierTransformₗᵢ ℝ ℂ).enorm_map _
    _ = _ := Lp.enorm_toLp hf₂

end D5.S3.Analytic.Fourier.RawFourierL2
