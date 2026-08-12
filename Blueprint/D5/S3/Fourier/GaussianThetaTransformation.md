# Gaussian Theta Transformation

## Abstract

The positive-real Gaussian theta sum transforms by reciprocal scaling.

**Theorem 1.1 (The Gaussian theta sum transforms by reciprocal scaling).**

$$\forall t\in\mathbb{R},\ 0<t \Rightarrow \sum_{n\in\mathbb{Z}}\operatorname{exp}(-\pi\,t\,n^{2}) = t^{-\frac{1}{2}}\sum_{n\in\mathbb{Z}}\operatorname{exp}(-\pi\,t^{-1}\,n^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GaussianThetaTransformation.gaussian_theta_transformation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real t, the sum over all integers n of exp(-pi t n^2) equals t^(-1/2) times the same sum with t replaced by 1/t. Pinned Mathlib proves exactly this real Gaussian transformation using Poisson summation, so the Lean declaration is a thin repository-addressed wrapper.

## References

- Truth anchor: `D5/S3/Fourier/GaussianThetaTransformation.gaussian_theta_transformation`
