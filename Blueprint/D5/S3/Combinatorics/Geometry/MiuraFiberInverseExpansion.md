# Actual reduction paths read complete indexed lengths

## Abstract

Actual reduction paths read complete indexed lengths.

**Theorem 1.1 (Every actual source has supported weights).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberInverseExpansion.reduction_indexed_active`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraFiberInverseExpansion.reduction_indexed_active` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal joint reduction from an actual residual array g to an actual height array h supplies supported nonnegative weights on both axes of h. The source dimensions are the core dimensions plus the respective complete weight sums. The occupied positions of g are exactly the cumulative weighted positions of the occupied lines of h. To undo a deletion, locate its surviving inactive position between cumulative core coordinates. The least core coordinate at or beyond that position is frozen, so its weight can be incremented. The exact contraction maps transport all occupied positions; transposition supplies the corresponding row step. The construction follows the actual reduction path and applies to all individual source height functions.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberInverseExpansion.reduction_indexed_active`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreTranspose](MiuraCoreTranspose.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberIndexed](MiuraFiberIndexed.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberInverse](MiuraFiberInverse.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberReadback](MiuraFiberReadback.md)
