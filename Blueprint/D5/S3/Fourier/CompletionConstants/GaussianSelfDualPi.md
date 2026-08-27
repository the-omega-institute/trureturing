# Gaussian Fourier Self-Duality

## Abstract

The standard real Fourier transform fixes a positive Gaussian exactly at scale pi.

**Theorem 1.1 (The positive Gaussian is strictly self-dual exactly at scale pi).**

$$\forall a\in \mathbb{R}, 0<a \Rightarrow (\widehat{(x \mapsto \operatorname{exp}(-a\,x^{2}))} = (x \mapsto \operatorname{exp}(-a\,x^{2})) \iff a = \pi).$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi.gaussian_self_dual_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fourier transform is Mathlib's standard real transform, whose kernel is exp(-2 pi i x xi). The real Gaussian is embedded into the complex codomain of that transform.

At frequency zero, self-duality and the pinned Gaussian integral give sqrt(pi/a) = 1, hence a = pi because a is positive. Conversely, the pinned Fourier-Gaussian formula at unit normalized scale gives strict self-duality when a = pi.

## References

- Truth anchor: `D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi.gaussian_self_dual_iff`
