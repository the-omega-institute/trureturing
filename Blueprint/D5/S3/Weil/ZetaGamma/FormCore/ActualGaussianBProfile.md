# The actual Gaussian source and its even B image

## Abstract

Evaluate the original complete theta transform and actual even B image of the same literal physical Gaussian source.

**Theorem 1.1 (Complete source identification with convergent tails).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualGaussianBProfile.actual_gaussian_suzuki_evenB`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualGaussianBProfile.actual_gaussian_suzuki_evenB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each nonnegative site a, take the original physical source F(x)=exp(9a/2-exp(2a)x). Its actual Gamma profile is integrable, and every translated exp(-5s/4)-weighted right-tail integrand at t at least zero is integrable. The actual even B profile is exactly cPhi*Phi(a+|r|), with cPhi=pi^(1/4)/4 and the original factor two in the even-B definition.

The complete theta series is evaluated by an actual HasSum calculation, including every positive theta mode. The right tail is then evaluated by a differentiable primitive whose weighted value tends to zero at infinity. Existing complete theta-jet bounds pay integrability and the endpoint. No linearity of the B map or profile identity is assumed.

This repository-derived source calculation supplies the normalization and actual source match for compact theta-cusp approximation. It does not infer a logarithmic Gamma form domain from H6 alone, extend a theorem to all of V, assert a noncompact signed Weil formula, or prove RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualGaussianBProfile.actual_gaussian_suzuki_evenB`
- Dependency: [D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity](../../../Analytic/Fourier/ThetaCuspConvolutionRegularity.md)
- Dependency: [D5/S3/Analytic/Fourier/XiThetaTransform](../../../Analytic/Fourier/XiThetaTransform.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge](ActualSuzukiMeanCharge.md)
