# Normalized binary projective rank polynomial

## Abstract

The actual binary projective rank sum has an exact product normalization over every field.

**Theorem 1.1 (Exact normalized evaluation).**

$$\forall d \in \mathbb{N},\; \forall R \in Fields,\; \forall q \in \operatorname{Nonzero}\left(R\right),\; \operatorname{W}\left(d, q\right) = \operatorname{P}\left(d, q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial.normalized_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For dimension d, take every subset U of the nonzero vectors of the binary d-dimensional space. The normalized rank sum W(d,q) adds (-1)^|U| times (q^(-1)) raised to the binary dimension of the span of U. The factor P(d,q) is the product of (1 - 2^j/q) over 0 <= j < d. These definitions include the empty projective configuration.

This is the normalized form of the classical characteristic polynomial of binary projective geometry in the Crapo–Rota framework. The proof counts injections using inclusion–exclusion at sizes 2^m, then uses infinitely many integral evaluations and specializes the polynomial identity in the given field. The mathematical use here is the unbounded signed-marginal obstruction in the accompanying graph-state coverage classification.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial.normalized_factor`
