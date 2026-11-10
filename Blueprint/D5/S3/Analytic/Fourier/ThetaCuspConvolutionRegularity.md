# Complete theta cusp convolution regularity

## Abstract

C2 regularity and the explicit cusp jump for convolution with the complete translated theta kernel.

**Theorem 1.1 (The complete translated theta convolution is C2).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity.actual_phi_shifted_cusp_convolution_C2`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity.actual_phi_shifted_cusp_convolution_C2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>=0 and every continuous integrable real density b, the literal convolution x↦∫ Phi(a+|x-y|)b(y)dy is C2. Its ordinary second derivative is the convolution with Phi''(a+|x-y|), plus the exact cusp term 2*Phi'(a)b(x), including the a=0 evenness case.

The proof differentiates the moving cusp away from its single integration point by dominated locally Lipschitz differentiation. It splits the signed first jet into a continuously differentiable part and a right-step jump; the step integrates to the lower cumulative primitive, whose ordinary FTC derivative is b(x). Complete theta jets and their exponential bounds are retained, including the separately paid first mode.

This is a repository-derived regularity theorem for the fixed complete theta kernel. It does not assert Gaussian Gamma-domain membership, Suzuki spectral nonvanishing, positivity of arbitrary physical Gram matrices, or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity.actual_phi_shifted_cusp_convolution_C2`
- Dependency: [D5/S3/Analytic/Fourier/ThetaRadialCurvature](ThetaRadialCurvature.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalPrimalTailProjection](../../Zeros/Jensen/OriginalPrimalTailProjection.md)
