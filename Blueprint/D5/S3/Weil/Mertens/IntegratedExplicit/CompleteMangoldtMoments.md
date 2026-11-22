# Differentiating throughout the initial half-plane

## Abstract

The signed logarithmic moments of the complete Mangoldt remainder

**Theorem 1.1 (All derivatives of the complete transform).**

$$\forall k \in \mathbb{N},\; \forall s \in \mathbb{C},\; 1 < \operatorname{Re}\left(s\right) \Rightarrow \left(\operatorname{IntegrableOn}\left((\lambda u \mapsto (-u)^{k} \cdot \operatorname{exp}\left(-\left(s \cdot u\right)\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(u\right)\right)), \operatorname{Ioi}\left(0\right)\right) \land \operatorname{iteratedDeriv}\left(k, transform, s\right) = \int_{0}^{\infty} (-u)^{k} \cdot \operatorname{exp}\left(-\left(s \cdot u\right)\right) \cdot \operatorname{U}\left(\operatorname{exp}\left(u\right)\right) du\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments.iterated_derivative_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Φ be the explicit transform of the complete Mangoldt remainder U. One derivative of exp(−su) contributes −u. Iterating gives the signed powers in the formula.

Fix s with Re(s)>1 and put d=(Re(s)−1)/3 and a=1+d. On a neighborhood of s, the damping beyond a is at least d. The exponential series gives uᵏ≤k! exp(du)/dᵏ for u≥0. The absolute zeroth moment on the line a thus dominates the moment of each fixed order throughout this neighborhood, including the next order used for differentiation. Differentiation under the integral and induction identify the derivatives.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments.iterated_derivative_moment`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaurent](CompleteMangoldtLaurent.md)
