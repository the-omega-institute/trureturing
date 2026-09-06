/- GID: D5/S3/Fourier/DyadicConvolutionDensity
   generality: I
   mirror-B: D5/B/S3/Fourier/DyadicConvolutionDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite dyadic convolution densities have the prescribed Fourier-Laplace products. -/

/- Library-search audit trail (2026-09-07):
   * D5: `dyadicConvolution`, `partial_convolution`, and `infinite convolution`
     found only InfiniteSincProduct's component densities and product theorem.
     ConvolutionPowerAmplification.fourierLaplace_convolve_complex requires
     smooth WeilTestFunction inputs, excluding uniform interval densities.
   * Pinned Mathlib v4.33.0: `integral_convolution`,
     `Integrable.integrable_convolution`, `support_convolution_subset`, and
     `HasProdUniformlyOn.tendstoUniformlyOn_finsetRange` supply the general
     integration and convergence machinery. `fourier_mul_convolution_eq`
     concerns real frequencies. No `infinite convolution` declaration was
     found by textual search of Mathlib.
   * GitHub repository searches via NyxID: `Lean4 "infinite convolution"`
     returned zero; `convolution language:Lean` returned the Boolean-cube
     TalagrandConvolutionConjecture (README and tree inspected) and the finite
     Dirichlet-convolution formal-langlands-lab, neither matching this slice.
     `Lean "Fabius"` returned an unrelated agent plugin. Global code search
     for `"infinite convolution" language:Lean` returned HTTP 401;
     code-level third-party completeness is ASSUMED-UNVERIFIED.
   The finite sequence uses n+1 components: zero-fold convolution is a Dirac
   measure and has no Lebesgue density. This is only an index shift of the
   preregistered finite-convolution witness.
-/

import D5.S3.Fourier.InfiniteSincProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace D5.S3.Fourier.DyadicConvolutionDensity

open Filter MeasureTheory Set Topology
open D5.S3.Fourier.InfiniteSincProduct
open scoped Convolution Pointwise

noncomputable section

/-- The positive-sign convention used by the frozen uniform factors. -/
def densityFourierLaplace (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (f x : ℂ) * Complex.exp (Complex.I * z * x)

/-- The convolution of components indexed from zero through n. -/
def dyadicPartialConvolution (ell : ℝ) : ℕ → ℝ → ℝ
  | 0 => uniformIntervalDensity (dyadicHalfWidth ell 0)
  | n + 1 => (dyadicPartialConvolution ell n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      uniformIntervalDensity (dyadicHalfWidth ell (n + 1))

private def tilt (f : ℝ → ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (f x : ℂ) * Complex.exp (Complex.I * z * x)

private theorem tilt_convolution (f g : ℝ → ℝ) (z : ℂ) :
    tilt (f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) z =
      (tilt f z) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (tilt g z) := by
  funext x
  simp only [tilt, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with t
  push_cast
  have hexp : Complex.exp (Complex.I * z * (x : ℂ)) =
      Complex.exp (Complex.I * z * (t : ℂ)) *
        Complex.exp (Complex.I * z * ((x : ℂ) - t)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

private theorem tilt_uniform_integrable (a : ℝ) (z : ℂ) :
    Integrable (tilt (uniformIntervalDensity a) z) := by
  have heq : tilt (uniformIntervalDensity a) z =
      (Icc (-a) a).indicator
        (fun x : ℝ => ((2 * a : ℝ)⁻¹ : ℂ) * Complex.exp (Complex.I * z * x)) := by
    funext x
    by_cases hx : x ∈ Icc (-a) a <;> simp [tilt, uniformIntervalDensity, hx]
  rw [heq]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply Continuous.integrableOn_Icc
  fun_prop

private theorem tilt_partial_integrable (ell : ℝ) (n : ℕ) (z : ℂ) :
    Integrable (tilt (dyadicPartialConvolution ell n) z) := by
  induction n with
  | zero => exact tilt_uniform_integrable _ _
  | succ n ih =>
      rw [dyadicPartialConvolution, tilt_convolution]
      exact ih.integrable_convolution _ (tilt_uniform_integrable _ _)

/-- The finite-convolution bridge: n+1 interval components give n+1 factors. -/
theorem dyadic_partial_convolution_fourierLaplace (ell : ℝ) (n : ℕ) (z : ℂ) :
    densityFourierLaplace (dyadicPartialConvolution ell n) z =
      ∏ j ∈ Finset.range (n + 1),
        uniformIntervalFourierLaplace (dyadicHalfWidth ell j) z := by
  induction n with
  | zero => simp [dyadicPartialConvolution, densityFourierLaplace,
      uniformIntervalFourierLaplace]
  | succ n ih =>
      change (∫ x : ℝ, tilt
        ((dyadicPartialConvolution ell n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          uniformIntervalDensity (dyadicHalfWidth ell (n + 1))) z x) = _
      rw [tilt_convolution, integral_convolution _ (tilt_partial_integrable ell n z)
        (tilt_uniform_integrable _ _), Finset.prod_range_succ]
      change densityFourierLaplace (dyadicPartialConvolution ell n) z *
        uniformIntervalFourierLaplace (dyadicHalfWidth ell (n + 1)) z = _
      rw [ih]

theorem dyadicPartialConvolution_integrable (ell : ℝ) (n : ℕ) :
    Integrable (dyadicPartialConvolution ell n) := by
  induction n with
  | zero => exact uniformIntervalDensity_integrable _
  | succ n ih => exact ih.integrable_convolution _ (uniformIntervalDensity_integrable _)

theorem dyadicPartialConvolution_nonneg (ell : ℝ) (hell : 0 < ell) (n : ℕ) (x : ℝ) :
    0 ≤ dyadicPartialConvolution ell n x := by
  have hp (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  induction n generalizing x with
  | zero => exact uniformIntervalDensity_nonneg (hp 0) x
  | succ n ih =>
      exact integral_nonneg (fun t =>
        mul_nonneg (ih t) (uniformIntervalDensity_nonneg (hp (n + 1)) (x - t)))

theorem integral_dyadicPartialConvolution (ell : ℝ) (hell : 0 < ell) (n : ℕ) :
    ∫ x : ℝ, dyadicPartialConvolution ell n x = 1 := by
  have hp (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  induction n with
  | zero => exact integral_uniformIntervalDensity (hp 0)
  | succ n ih =>
      rw [dyadicPartialConvolution, integral_convolution _
        (dyadicPartialConvolution_integrable ell n) (uniformIntervalDensity_integrable _)]
      simp [ih, integral_uniformIntervalDensity (hp (n + 1))]

#print axioms dyadic_partial_convolution_fourierLaplace

end

end D5.S3.Fourier.DyadicConvolutionDensity
