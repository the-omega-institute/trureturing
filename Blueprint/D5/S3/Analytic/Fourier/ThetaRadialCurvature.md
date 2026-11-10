# Radial curvature of the original theta kernel

## Abstract

Classical radial curvature and square-variable strict concavity for the complete theta kernel.

**Theorem 1.1 (The actual radial curvature inequality and strict concavity).**

Lean statement: `D5/S3/Analytic/Fourier/ThetaRadialCurvature.actual_phi_radial_curvature_and_square_concavity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/ThetaRadialCurvature.actual_phi_radial_curvature_and_square_concavity` (`✓ std3`). ∎

*Citation.* George Csordas (2013). *Fourier transforms of positive definite kernels and the Riemann xi-Function*. URL: <https://arxiv.org/abs/1309.0055v2>.

*Commentary.*

Let Phi be romikPhi, the literal original theta series, and let primes denote ordinary derivatives in its real argument. For every x>0, x*((Phi'(x))^2-Phi(x)*Phi''(x))+Phi(x)*Phi'(x)>0. Moreover, r↦log(Phi(sqrt(r))) is strictly concave on the entire open ray r>0.

This is a known result. Csordas, arXiv:1309.0055v2, Theorem 4.2(b), attributes square-variable strict concavity to Csordas and Varga, Moment inequalities and the Riemann hypothesis (1988), Theorem 2.1. Remark 4.3(a) gives the radial curvature formulation. With K in that source's normalization, Phi(x)=2*K(x/2), so positive scaling and r↦r/4 preserve the asserted strict concavity.

The proof works directly with the canonical theta derivative modes. After setting y=pi*exp(2*x), it treats modes one and two exactly and retains every n>=3 mode in an absolutely summable quadratic-exponential tail. The polynomial bounds hold uniformly for y>=3; the complete normalized fourth-log numerator retains a negative reserve of at least 12623/64000 times 256*y^5*Q0(y) after tail perturbation. Positivity of Phi and its evenness pay the logarithmic denominators and vanishing odd origin jets. Two derivative-sign arguments then give the radial gap and strict concavity. The finite rational comparisons organize this infinite analytic proof; no theta mode is discarded.

The result supplies the actual square-variable concavity used in Suzuki's reflected physical-kernel comparison, including its diagonal case. The conclusion concerns r>0; the theorem introduces no curvature hypothesis and makes no assertion of the Riemann hypothesis. The contribution here is a concrete formal proof for the fixed source, rather than a claim of a new classical concavity theorem.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/ThetaRadialCurvature.actual_phi_radial_curvature_and_square_concavity`
- Dependency: [D5/S3/Analytic/Fourier/ThetaDifferentialKernel](ThetaDifferentialKernel.md)
- Dependency: [D5/S3/Zeros/Jensen/OriginalPrimalTailProjection](../../Zeros/Jensen/OriginalPrimalTailProjection.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceThetaMomentBounds](../../Zeros/Jensen/SourceThetaMomentBounds.md)
