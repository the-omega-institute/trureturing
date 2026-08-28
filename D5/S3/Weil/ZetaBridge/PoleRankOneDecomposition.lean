/- GID: D5/S3/Weil/ZetaBridge/PoleRankOneDecomposition
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PoleRankOneDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the pole pair of a convolution square with one boundary-readout energy. -/

import D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds

namespace D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition

open MeasureTheory
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds

open scoped ComplexConjugate

noncomputable section

private theorem fourierLaplace_I_div_two_eq_boundary_readout (f : WeilTestFunction) :
    fourierLaplace f (Complex.I / 2) =
      ∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x := by
  unfold fourierLaplace fourierKernel
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The two completed-zeta pole evaluations of a convolution square are twice the squared
modulus of its `1 / 2` Fourier-Laplace boundary observation. -/
theorem pole_rank_one_decomposition (f : WeilTestFunction) :
    poleTerm (convolutionSquare f) =
      2 * (Complex.normSq (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) : ℂ) := by
  have hEven : fourierLaplace f (-Complex.I / 2) = fourierLaplace f (Complex.I / 2) := by
    simpa only [neg_div] using fourierLaplace_neg f (Complex.I / 2)
  have hConjPos : conj (Complex.I / 2) = -Complex.I / 2 := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
  have hConjNeg : conj (-Complex.I / 2) = Complex.I / 2 := by
    rw [show -Complex.I / 2 = -(Complex.I / 2) by ring, map_neg, hConjPos]
    ring
  rw [poleTerm, fourierLaplace_convolutionSquare_complex,
    fourierLaplace_convolutionSquare_complex]
  rw [hConjNeg, hConjPos, hEven, fourierLaplace_I_div_two_eq_boundary_readout]
  rw [Complex.mul_conj]
  ring

#print axioms pole_rank_one_decomposition

end

end D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition
