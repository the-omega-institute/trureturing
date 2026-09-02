# Scale-Shape Separation

## Abstract

Positive overall scaling preserves spectral-zeta zeros; only shape can change them.

**Theorem 1.1 (Overall scale does not move spectral-zeta zeros).**

$$\begin{aligned}\forall a: \mathbb{R}, 0 < a \Rightarrow\\\forall lambda: \mathbb{N}\to\mathbb{R}, (\forall n: \mathbb{N}, 0 < lambda\left(n\right)) \Rightarrow\\{}\operatorname{spectralZeroSet}\left(\operatorname{scaleSpectrum}\left(a, lambda\right)\right) = \operatorname{spectralZeroSet}\left(lambda\right) \land\\{}\forall b: \mathbb{R}, 0 < b \Rightarrow \forall mu: \mathbb{N}\to\mathbb{R}, (\forall n: \mathbb{N}, 0 < mu\left(n\right)) \Rightarrow \neg \operatorname{spectralZeroSet}\left(\operatorname{scaleSpectrum}\left(a, lambda\right)\right) = \operatorname{spectralZeroSet}\left(\operatorname{scaleSpectrum}\left(b, mu\right)\right) \Rightarrow \neg lambda = mu.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Dilation/ScaleShapeSeparation.scale_shape_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive spectrum is represented by a positive real sequence lambda. Its overall scale a produces the spectrum n maps to a lambda(n), and its raw Dirichlet zero set contains exactly those complex s where the spectral terms are summable and spectralZeta(lambda,s) vanishes.

The first conjunct identifies the zero set after positive scaling with the original zero set. The second conjunct states the corresponding only-if direction: if two positively scaled spectra have different zero sets, their dimensionless shape sequences are different.

The factorization Z_(a lambda)(s)=a^(-s) Z_lambda(s) follows termwise from complex powers. Positivity makes the scale factor nonzero, so it preserves both summability of the terms and vanishing of their sum.

## References

- Truth anchor: `D5/S3/Analytic/Dilation/ScaleShapeSeparation.scale_shape_separation`
- Dependency: [D5/S3/Analytic/Asymptotics/SpectralZetaContinuation](../Asymptotics/SpectralZetaContinuation.md)
