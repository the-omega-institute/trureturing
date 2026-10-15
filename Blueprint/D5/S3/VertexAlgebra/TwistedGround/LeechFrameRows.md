# Literal Leech Gram Rows

## Abstract

Exact integer Gram rows factor the literal hyperbolic frame calculation.

**Theorem 1.1 (Literal Leech Gram Rows).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/LeechFrameRows.literalGramRows_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/LeechFrameRows.literalGramRows_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rows of R are the twenty-four literal integral binary frame vectors. The matrix literalGramRows is exactly R times the original ExplicitLeechBasis.gramMatrix. Thus the pairing of two frame rows is the dot product of a literal Gram row with the other integral vector.

This integer factorization preserves the full original quadratic and polar calculation. It neither substitutes an ambient-coordinate form nor enumerates the 2^24 charges. The resulting entries are used to certify the original hyperbolic basis and its native representation action.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/LeechFrameRows.literalGramRows_eq`
- Dependency: [D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice](../GolayLeech/ExplicitLeechLattice.md)
