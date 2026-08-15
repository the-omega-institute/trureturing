/- GID: D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/ConvolutionSquarePositivity
   mirror-E: none(waiver:structural-closure-properties-only)
   anchors: []
   digest: Bridge Fourier normalizations and prove convolution-square spectral positivity. -/

import D5.S3.Weil.FourierLaplace
import Mathlib.Analysis.Fourier.Convolution

namespace D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity

open MeasureTheory
open D5.S3.Weil.Convention D5.S3.Weil.FourierLaplace
open scoped ComplexConjugate Convolution FourierTransform

/-- The angular-frequency transform agrees with mathlib's `2 * pi` normalization. -/
theorem fourierLaplace_real_eq_fourier (g : WeilTestFunction) (xi : ℝ) :
    fourierLaplace g xi = 𝓕 (g : ℝ → ℂ) (mathlibFrequency xi) := by
  rw [fourierLaplace_apply, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [mathlibFrequency, Real.inner_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- A convolution square transforms to the squared norm of the original transform. -/
theorem fourierLaplace_convolutionSquare_real (g : WeilTestFunction) (xi : ℝ) :
    fourierLaplace (convolutionSquare g) xi =
      (Complex.normSq (fourierLaplace g xi) : ℂ) := by
  rw [fourierLaplace_real_eq_fourier]
  have hconvolution :
      ((convolutionSquare g : WeilTestFunction) : ℝ → ℂ) =
        (g : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (involution g : ℝ → ℂ) := by
    funext x
    rfl
  have hg_integrable : Integrable (g : ℝ → ℂ) := g.integrable
  have hinvolution_integrable : Integrable (involution g : ℝ → ℂ) :=
    (involution g).integrable
  have hg_continuous : Continuous (g : ℝ → ℂ) := g.continuous
  have hinvolution_continuous : Continuous (involution g : ℝ → ℂ) :=
    (involution g).continuous
  rw [hconvolution]
  rw [Real.fourier_mul_convolution_eq] <;> try assumption
  rw [← fourierLaplace_real_eq_fourier g xi]
  rw [← fourierLaplace_real_eq_fourier (involution g) xi]
  rw [fourierLaplace_involution_real, Complex.mul_conj]

/-- The transform of a convolution square is real and nonnegative on the real axis. -/
theorem fourierLaplace_convolutionSquare_real_nonnegative (g : WeilTestFunction) (xi : ℝ) :
    (fourierLaplace (convolutionSquare g) xi).im = 0 ∧
      0 ≤ (fourierLaplace (convolutionSquare g) xi).re := by
  rw [fourierLaplace_convolutionSquare_real]
  exact ⟨by simp, Complex.normSq_nonneg _⟩

example (g : WeilTestFunction) :
    0 ≤ (fourierLaplace (convolutionSquare g) 0).re :=
  (fourierLaplace_convolutionSquare_real_nonnegative g 0).2

end D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
