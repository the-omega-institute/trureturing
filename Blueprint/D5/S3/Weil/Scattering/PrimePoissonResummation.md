# Prime Poisson Resummation

## Abstract

The weighted bilateral translation history of one prime is the centered unitary Poisson resolvent without a remainder.

**Theorem 1.1 (Prime-power translation histories resum exactly).**

$$\forall p \in \mathbb{N}, psi \in \operatorname{Ltwo}\left(\mathbb{R}, \mathbb{C}\right),\; \operatorname{Prime}\left(p\right) \Rightarrow \operatorname{let} r: \mathbb{R} = \frac{1}{\operatorname{sqrt}\left(p\right)}; \operatorname{let} U: \operatorname{Ltwo}\left(\mathbb{R}, \mathbb{C}\right) \to \operatorname{Ltwo}\left(\mathbb{R}, \mathbb{C}\right) = \operatorname{realTranslation}\left(\operatorname{log}\left(p\right)\right); -\operatorname{log}\left(p\right) \times \sum_{n=0}^{\infty} r^{n + 1} \times [\operatorname{inner}\left(psi, \operatorname{apply}\left(U^{n + 1}, psi\right)\right) + \operatorname{inner}\left(psi, \operatorname{apply}\left(\operatorname{adjoint}\left(U\right)^{n + 1}, psi\right)\right)] = -\operatorname{log}\left(p\right) \times \operatorname{inner}\left(psi, \operatorname{apply}\left(\operatorname{unitaryPoissonOperator}\left(r, U\right) - \operatorname{identity}\left(\right), psi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Scattering/PrimePoissonResummation.prime_poisson_resummation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a prime p, the radius is one over square root p and the unitary is real-line L2 translation by log p. Both constructions are displayed in the statement.

The left side is the complete positive-index bilateral orbit series. The right side uses the independently resolvent-defined Poisson operator, so the equality records the local Neumann bridge rather than installing the series by definition.

## References

- Truth anchor: `D5/S3/Weil/Scattering/PrimePoissonResummation.prime_poisson_resummation`
