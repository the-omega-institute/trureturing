# Gaussian Schwartz Maps

## Abstract

The standard Gaussian has rapid decay at every derivative order.

**Theorem 1.1 (A Gaussian Schwartz map on every real inner product space).**

$$\forall E \in RealInnerProductSpace,\; \exists f \in \operatorname{Schwartz}\left(E, \mathbb{R}\right),\; \forall x \in E,\; f\left(x\right) = \exp(-\frac{\Vert x\Vert^{2}}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/GaussianSchwartz.exists_gaussian_schwartz` (`✓ std3`). ∎

*Citation.* Gregory J. Loges (2026). *Gaussians in inner product spaces as Schwartz maps*. URL: <https://github.com/HEPLean/PhysLean/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/Physlib/Mathematics/InnerProductSpace/Gaussian.lean>.

*Commentary.*

Let E be a real normed inner product space. There is a real Schwartz map f on E whose value at each x is exp(-norm(x) squared / 2). Completeness and finite dimensionality are not required.

The derivatives of the squared norm are bounded by powers of 2 plus the squared norm. The chain rule bounds each Gaussian derivative by a polynomial times the same Gaussian. Exponential decay bounds the tail, and a maximum on a compact interval bounds the remaining values.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/GaussianSchwartz.exists_gaussian_schwartz`
