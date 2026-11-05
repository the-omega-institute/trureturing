# The general-parameter Gaussian Laplace identity

## Abstract

Original Mills normalization and complete classification.

**Theorem 1.1 (General-parameter Gaussian convolution kernel identity).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_kernel_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_kernel_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a and t, the source kernel G_a(t) equals t^3/4 times the integral from zero to one of (1+(2a-1)v^2) exp(-(1+v^2)t^2/4). Integrating the derivative of v exp(-(1+v^2)t^2/4) gives exp(-t^2/2) as the integral of (1-t^2 v^2/2) times the same exponential. Substitution in G and linearity of the integral give the stated identity. This is the source's pointwise identity (2.3).

**Theorem 1.2 (The negative-parameter Gaussian kernel is the original K kernel).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_kernel_eq_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_kernel_eq_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A second interval integration by parts gives G_(-1)(t)=K(t), preserving the original Gaussian convolution normalization and the exact K supplier.

**Theorem 1.3 (The exact general-parameter Gaussian Laplace identity).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_laplace_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_laplace_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Mills Laplace formula and square convolution are combined with the original kernelLaplace identity at parameter -1. A direct integration by parts gives the t times Gaussian integral, and linearity in a then yields Y_(a,a-2)(x)-(a-1)=integral exp(-xt) G_a(t) for every x>0.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_kernel_eq_K`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_kernel_identity`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/GaussianLaplace.gaussian_laplace_identity`
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/Result](Result.md)
