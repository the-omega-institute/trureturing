/- GID: D5/S3/Analysis/MixedFourierKernel
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A mixed-sign Fourier transform of an integrable two-variable kernel under Schwartz test pairings. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod

/-!
Omega original.

A mixed-sign Fourier transform of an integrable two-variable kernel under
Schwartz test pairings.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform

namespace Omega

private def phase (s ξ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * s * ξ : ℝ) : ℂ) * Complex.I)

private theorem norm_phase (s ξ : ℝ) : ‖phase s ξ‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem phase_continuous : Continuous (fun z : ℝ × ℝ => phase z.1 z.2) := by
  unfold phase
  fun_prop

/-- The ordinary mixed Fourier transform of a kernel relative to Lebesgue measure. -/
def mixedFourier (K : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  ∫ q : ℝ × ℝ, star (phase q.1 p.1) * phase q.2 p.2 * K q
    ∂((volume : Measure ℝ).prod volume)

private theorem phase_inverse_integral (f : SchwartzMap ℝ ℂ) (s : ℝ) :
    (∫ ξ : ℝ, phase s ξ * 𝓕 f ξ) = f s := by
  have hi : (𝓕⁻ (𝓕 f) : SchwartzMap ℝ ℂ) = f := FourierTransform.fourierInv_fourier_eq f
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g s) hi
  change (𝓕⁻ (𝓕 f) : SchwartzMap ℝ ℂ) s = f s at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [phase, Real.inner_apply, smul_eq_mul]
  congr 3
  ring

/-- Fourier inversion on both Schwartz factors recovers the position-space pairing. -/
theorem mixedFourier_pairing (K : ℝ × ℝ → ℂ)
    (hK : Integrable K ((volume : Measure ℝ).prod volume)) (f g : SchwartzMap ℝ ℂ) :
    (∫ p : ℝ × ℝ, star (𝓕 f p.1) * mixedFourier K p * 𝓕 g p.2
      ∂((volume : Measure ℝ).prod volume)) =
      ∫ q : ℝ × ℝ, star (f q.1) * K q * g q.2
        ∂((volume : Measure ℝ).prod volume) := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let H : (ℝ × ℝ) × (ℝ × ℝ) → ℂ := fun z =>
    star (𝓕 f z.1.1) * (star (phase z.2.1 z.1.1) * phase z.2.2 z.1.2 * K z.2) *
      𝓕 g z.1.2
  have hp₁ : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => phase z.2.1 z.1.1) :=
    phase_continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.comp continuous_fst))
  have hp₂ : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => phase z.2.2 z.1.2) :=
    phase_continuous.comp ((continuous_snd.comp continuous_snd).prodMk
      (continuous_snd.comp continuous_fst))
  have hi : Integrable H (μ.prod μ) := by
    have hfm := (𝓕 f : SchwartzMap ℝ ℂ).continuous.comp
      (continuous_fst.comp continuous_fst : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.1))
    have hgm := (𝓕 g : SchwartzMap ℝ ℂ).continuous.comp
      (continuous_snd.comp continuous_fst : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => z.1.2))
    have hk : AEStronglyMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => K z.2)
        (μ.prod μ) := hK.aestronglyMeasurable.comp_snd
    have hm : AEStronglyMeasurable H (μ.prod μ) :=
      (hfm.star.aestronglyMeasurable.mul
        ((hp₁.star.mul hp₂).aestronglyMeasurable.mul hk)).mul hgm.aestronglyMeasurable
    refine (((𝓕 f : SchwartzMap ℝ ℂ).integrable.norm.mul_prod
      (𝓕 g : SchwartzMap ℝ ℂ).integrable.norm).mul_prod hK.norm).mono' hm ?_
    filter_upwards with z
    simp only [H, norm_mul, norm_star, norm_phase, mul_one, one_mul]
    exact le_of_eq (by ring)
  have houter (p : ℝ × ℝ) : star (𝓕 f p.1) * mixedFourier K p * 𝓕 g p.2 =
      ∫ q, H (p, q) ∂μ := by
    simp only [mixedFourier, H, integral_mul_const, integral_const_mul, μ]
  have hinner (q : ℝ × ℝ) : (∫ p, H (p, q) ∂μ) = star (f q.1) * K q * g q.2 := by
    have hmul (p : ℝ × ℝ) :
        H (p, q) = K q * (star (phase q.1 p.1 * 𝓕 f p.1) * (phase q.2 p.2 * 𝓕 g p.2)) := by
      simp only [H, star_mul]
      ring
    simp_rw [hmul, integral_const_mul]
    rw [integral_prod_mul (fun ξ => star (phase q.1 ξ * 𝓕 f ξ))
      (fun ξ => phase q.2 ξ * 𝓕 g ξ)]
    simp only [Complex.star_def, integral_conj, phase_inverse_integral]
    ring
  have h := integral_integral_swap (f := fun p q => H (p, q)) hi
  simpa only [houter, hinner] using h

end Omega

