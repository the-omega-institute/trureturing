# Pointwise literal energy enclosures

## Abstract

Pointwise literal energy enclosures.

**Theorem 1.1 (Every point of an accepted cell).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Cell.checked_canonical_cell_normSq_encloses`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Cell.checked_canonical_cell_normSq_encloses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R be a natural radius, p and q rational polynomials with supplied coefficient lists, and s a rational shift. A successful canonical cell check verifies the positive radius, the cell endpoints, four cutoff endpoint checks, exact even polynomial provenance and all signed expression bounds.

For every real y in the returned closed cell, the annotated norm-square expression encloses the squared complex norm of H(y)-H(y-s), where H is smoothTransition(2-|y|/R) times the evenized complex polynomial p+i q. Endpoint and shifted cutoff intervals use the same exact scalar function.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Cell.checked_canonical_cell_normSq_encloses`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Coefficients](Coefficients.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic](Scalar/Logistic.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Source](Source.md)
- Dependency: [D5/S3/Weil/TestFunctions/RationalCutoffApproximation](../../TestFunctions/RationalCutoffApproximation.md)
