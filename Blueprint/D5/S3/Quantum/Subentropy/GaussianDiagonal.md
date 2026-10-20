# The diagonal Gaussian entropy expectation

## Abstract

A fixed coordinate entropy expectation is the common baseline for diagonal subentropy.

For a finite probability vector p, use independent standard real Gaussian coordinates z_(i,0), z_(i,1), put X_i=(z_(i,0)^2+z_(i,1)^2)/2 and a=Σ_i p_i X_i. Write η(u)=−u log u. Choose any coordinate i₀; the theorem does not require positive weights.

**Theorem 1.1 (A common fixed-dimension entropy baseline).**

$$\operatorname{Integrable}\left(\operatorname{eta}\left(a\right), gamma\right) \land \operatorname{Q}\left(\operatorname{diag}\left(p\right)\right) = \operatorname{E}\left(\operatorname{eta}\left(a\right)\right) - \operatorname{E}\left(\operatorname{eta}\left(\operatorname{X}\left(i0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/GaussianDiagonal.diagonal_subentropy_gaussian_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Swapping two coordinate pairs preserves the product Gaussian measure, so all expectations Eη(X_i) are equal. A fourth-moment Gaussian bound supplies absolute integrability of each coordinate entropy. The Gaussian entropy-gap representation and the integrable finite baseline then imply integrability of η(a). Integrating the difference and using Σ_i p_i=1 gives Q(diag p)=Eη(a)−Eη(X_(i₀)). The baseline is constant within each fixed dimension, which suffices for cancellation in fixed-dimension concavity and pinching comparisons.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/GaussianDiagonal.diagonal_subentropy_gaussian_entropy`
- Dependency: [D5/S3/Quantum/Subentropy/GaussianEntropy](GaussianEntropy.md)
