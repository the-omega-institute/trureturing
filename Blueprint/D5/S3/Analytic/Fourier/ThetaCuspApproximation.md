# Compact approximation of the complete theta cusp

## Abstract

Compact smooth even approximation of the complete translated Gaussian theta profile, with one common weighted jet budget for every nonnegative shift and the original cusp jump retained.

**Theorem 1.1 (One sequence pays the compact Weil interface).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaCuspApproximation.actual_gaussian_cusp_compact_approximation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaCuspApproximation.actual_gaussian_cusp_compact_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one common nonnegative constant C for every nonnegative shift a and every approximation index n. Each actual sequence of compactly supported, even C-infinity Weil tests converges to cPhi*Phi(a+|x|) in the exp(|x|/2)-weighted L1 norm. The same C bounds every closed-strip zeroth-plus-second derivative budget and every full-line exp(-|x|) pointwise envelope. The convergence is asserted for each shift; no convergence rate uniform in a is claimed.

The construction first convolves the complete shifted theta cusp with a nonnegative even normalized bump of radius 1/(n+1), then multiplies by a fixed even bump at scale n+1. Smoothness is supplied by the existing Mathlib compact smooth convolution theorem. The original cPhi=pi^(1/4)/4 normalization remains in the profile.

The second derivative is controlled by the existing exact cusp identity: the convolution with the complete second theta jet plus 2*Phi'(a) times the smoothing density. Positivity, unit mass and the density's radius bound pay the weighted jump integral. The full first theta jet has a global bound for all a at least zero, so the constant also remains uniform over the complete shift family. Derivative norms of the shrinking smoothing density are not used as an assumed uniform bound.

The uniform budget is consumed through the existing closed-strip Fourier-Laplace estimate. This supplies the approximation interface needed before dominated passage of the compact signed Weil formula; the theorem itself does not assert that noncompact formula, any positivity of the signed zero pairing, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/ThetaCuspApproximation.actual_gaussian_cusp_compact_approximation`
- Dependency: [D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity](ThetaCuspConvolutionRegularity.md)
- Dependency: [D5/S3/Weil/InterpolationJets/QuantitativeEvenSeed](../../Weil/InterpolationJets/QuantitativeEvenSeed.md)
- Dependency: [D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay](../../Weil/TestFunctions/FourierLaplaceClosedStripDecay.md)
