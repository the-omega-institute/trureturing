/- GID: D5/S3/Fourier/DyadicFourierInversion
   generality: I
   mirror-B: D5/B/S3/Fourier/DyadicFourierInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier inversion identifies the dyadic convolution density as a smooth function. -/

/- Library-search audit trail (2026-09-07):
   1. D5: searched dyadicConvolutionDensity_contDiff, fourier_inversion,
      contDiff_of_integrable, and contDiff/fourier combinations. No exact
      smoothness or inversion theorem for this density was found. Reuse
      DyadicTransformDecay.dyadic_density_transform_decay and
      DyadicConvolutionDensity.dyadicPartialConvolution_tendsto,
      dyadicConvolutionDensity_integrable, and its private dyadic_lipschitz
      estimate via the existing open-private mechanism. Both imports are I;
      InfiniteSincProduct and PaleyWiener were also checked and are I.
   2. Pinned Mathlib v4.33.0: searched fourierIntegralInv, fourier_inversion,
      contDiff_of_integrable, contDiff_fourier, and convolution continuity.
      Reuse Continuous.fourierInv_fourier_eq, Real.contDiff_fourier,
      Real.fourier_eq', Real.fourierInv_eq_fourier_neg, and integrable
      changes of variables. The documented fourier_inversion name is now
      fourierInv_fourier_eq. No direct theorem for the dyadic density hit.
   3. Third-party Lean ecosystem via NyxID GitHub observer: repository query
      Fourier language:Lean returned 18 repositories; Fabius language:Lean
      returned zero. The complete mean-fourier source tree concerns invariant
      means and almost periodic functions, with no dyadic density module.
      Global code query contDiff + fourier + language:Lean returned HTTP 401.
      Code-level completeness outside the searched scope is ASSUMED-UNVERIFIED.
   4. Local bridge: pass the frozen Lipschitz bound to the pointwise limit,
      rescale the weighted transform to Mathlib's -2*pi convention, and use
      the upstream inversion and smoothness theorems without reproving them.
      Preregistered witness: dyadic_density_eq_fourier_inversion, consumed
      by dyadicConvolutionDensity_contDiff to identify the original density.
-/

import D5.S3.Fourier.DyadicTransformDecay
import D5.S3.Fourier.DyadicConvolutionDensity
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace D5.S3.Fourier.DyadicFourierInversion

open Filter MeasureTheory Set Topology
open scoped FourierTransform
open D5.S3.Fourier.InfiniteSincProduct
open D5.S3.Fourier.DyadicConvolutionDensity
open D5.S3.Fourier.DyadicTransformDecay

open private dyadic_lipschitz from D5.S3.Fourier.DyadicConvolutionDensity

noncomputable section

private theorem density_continuous (ell : ℝ) (hell : 0 < ell) :
    Continuous (dyadicConvolutionDensity ell) := by
  let L : ℝ≥0 := ⟨(2 * dyadicHalfWidth ell 0)⁻¹ / dyadicHalfWidth ell 1, by
    unfold dyadicHalfWidth
    positivity⟩
  apply LipschitzWith.continuous (K := L)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq]
  exact le_of_tendsto'
    ((dyadicPartialConvolution_tendsto ell hell x).sub
      (dyadicPartialConvolution_tendsto ell hell y)).abs
    (fun n => dyadic_lipschitz ell hell n x y)

private theorem density_fourier_eq (ell xi : ℝ) :
    𝓕 (fun x : ℝ => (dyadicConvolutionDensity ell x : ℂ)) xi =
      densityFourierLaplace (dyadicConvolutionDensity ell) ((-2 * Real.pi * xi : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, densityFourierLaplace]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, mul_comm _ (dyadicConvolutionDensity ell x : ℂ)]
  congr 2
  push_cast
  ring

private theorem normalized_transform_weighted (ell : ℝ) (hell : 0 < ell) (k : ℕ) :
    Integrable (fun xi : ℝ => ‖xi‖ ^ k *
      ‖densityFourierLaplace (dyadicConvolutionDensity ell) ((-2 * Real.pi * xi : ℝ) : ℂ)‖) := by
  have hc : (-2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hw := ((dyadic_density_transform_decay ell hell k).comp_mul_left' hc).const_mul
    ((|-2 * Real.pi| ^ k)⁻¹)
  apply hw.congr
  filter_upwards with xi
  simp only [abs_mul, mul_pow, Real.norm_eq_abs]
  field_simp
  <;> ring

/-- Inversion recovers the actual real density from its rescaled Fourier-Laplace transform. -/
theorem dyadic_density_eq_fourier_inversion (ell : ℝ) (hell : 0 < ell) (x : ℝ) :
    dyadicConvolutionDensity ell x =
      (𝓕⁻ (fun xi : ℝ => densityFourierLaplace (dyadicConvolutionDensity ell)
        ((-2 * Real.pi * xi : ℝ) : ℂ)) x).re := by
  let f : ℝ → ℂ := fun t => (dyadicConvolutionDensity ell t : ℂ)
  have hi : Integrable f := (dyadicConvolutionDensity_integrable ell hell).ofReal
  have hc : Continuous f := Complex.continuous_ofReal.comp (density_continuous ell hell)
  have hfc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have hn : Integrable (fun xi : ℝ => ‖𝓕 f xi‖) := by
    simpa only [f, density_fourier_eq, pow_zero, one_mul] using
      normalized_transform_weighted ell hell 0
  have hfi : Integrable (𝓕 f) := (integrable_norm_iff hfc.aestronglyMeasurable).mp hn
  have hinv := congrFun (hc.fourierInv_fourier_eq hi hfi) x
  have heq : 𝓕 f = fun xi : ℝ => densityFourierLaplace (dyadicConvolutionDensity ell)
      ((-2 * Real.pi * xi : ℝ) : ℂ) := funext (density_fourier_eq ell)
  rw [heq] at hinv
  exact (congrArg Complex.re hinv).symm

/-- The dyadic convolution density is differentiable to every natural order. -/
theorem dyadicConvolutionDensity_contDiff (ell : ℝ) (hell : 0 < ell) (k : ℕ) :
    ContDiff ℝ k (dyadicConvolutionDensity ell) := by
  let F : ℝ → ℂ := fun xi => densityFourierLaplace (dyadicConvolutionDensity ell)
    ((-2 * Real.pi * xi : ℝ) : ℂ)
  have hF : ContDiff ℝ k (𝓕 F) := Real.contDiff_fourier (N := (k : ℕ∞))
    (fun n _ => normalized_transform_weighted ell hell n)
  have hinv : ContDiff ℝ k (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun x : ℝ => 𝓕 F (-x) :=
      funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hF.comp contDiff_id.neg
  convert Complex.reCLM.contDiff.comp hinv using 1
  ext x
  exact dyadic_density_eq_fourier_inversion ell hell x

#print axioms dyadic_density_eq_fourier_inversion
#print axioms dyadicConvolutionDensity_contDiff

end

end D5.S3.Fourier.DyadicFourierInversion
