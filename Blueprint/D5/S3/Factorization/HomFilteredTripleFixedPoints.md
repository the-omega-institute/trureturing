# Homomorphism-Filtered Triple Fixed Points

## Abstract

An additive homomorphism filters three-cycle fixed points by its kernel.

**Theorem 1.1 (Exact fixed-point count in a finite abelian group).**

$$\left(\left(t \ne 0 \land \left(3t = 0 \land \operatorname{f}\left(t\right) \ne 0\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{fixedBy}\left(\operatorname{HomTriple}\left(f\right), t\right)\right) = \frac{\operatorname{card}\left(G\right)}{3}\right) \land \left(\left(t \ne 0 \land \left(3t \ne 0 \lor \operatorname{f}\left(t\right) = 0\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{fixedBy}\left(\operatorname{HomTriple}\left(f\right), t\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/HomFilteredTripleFixedPoints.card_fixedBy_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A homomorphism-admissible triple has three distinct images. Translation preserves admissibility. A nonzero fixed translation must have order three; its three-cycle is admissible exactly when the homomorphism does not kill that direction. Every fixed triple is a translate of the cycle, and its stabilizer has order three. Unlike a cyclic group, a noncyclic group can have several eligible order-three direction subgroups.

## References

- Truth anchor: `D5/S3/Factorization/HomFilteredTripleFixedPoints.card_fixedBy_nonzero`
- Dependency: [D5/S3/Factorization/FiniteTranslationStabilizer](FiniteTranslationStabilizer.md)
