# Slope-Filtered Triple Fixed Points

## Abstract

Fixed points of three-abscissa translation after filtering by a slope.

**Theorem 1.1 (Exact fixed-point count for a nonzero translation).**

$$\left(\left(t \ne 0 \land \left(3t = 0 \land at \ne 0\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{fixedBy}\left(\operatorname{SlopeTriple}\left(n, a\right), t\right)\right) = \frac{n}{3}\right) \land \left(\left(t \ne 0 \land \left(3t \ne 0 \lor at = 0\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{fixedBy}\left(\operatorname{SlopeTriple}\left(n, a\right), t\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Collinear/SlopeFilteredTripleFixedPoints.card_fixedBy_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A slope-admissible triple is a three-element abscissa set on which multiplication by the slope is injective. Translation preserves this condition. A fixed triple is a three-cycle, which exists only when the translation has order three. Its image remains three distinct points exactly when the slope does not kill the translation direction. All fixed triples form one translation orbit, whose stabilizer has order three.

## References

- Truth anchor: `D5/S3/Factorization/Collinear/SlopeFilteredTripleFixedPoints.card_fixedBy_nonzero`
- Dependency: [D5/S3/Factorization/FiniteTranslationStabilizer](../FiniteTranslationStabilizer.md)
