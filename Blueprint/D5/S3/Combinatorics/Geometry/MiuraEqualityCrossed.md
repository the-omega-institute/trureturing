# MiuraEqualityCrossed

## Abstract

Actual-array geometric equality for the original Miura residual class.

**Theorem 1.1 (crossed equality four).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.crossed_equality_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.crossed_equality_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. If the ordered counts of minimum row slabs, maximum row slabs, minimum column slabs and maximum column slabs are either (1,2,2,1) or (2,1,1,2), the actual array has exactly four individual extrema. The first pattern derives its boundary slabs and excludes neutral slabs; height negation proves the other pattern without exchanging physical sides.

**Theorem 1.2 (equality two slabs or four).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.equality_two_slabs_or_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.equality_two_slabs_or_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array on an m by n grid with both dimensions at least two, suppose that each axis has a genuinely unoccupied row and that the individual-extremum count equals the sum of the actual frozen row-run count and the actual frozen column-run count. Either the row axis has exactly one minimum slab and one maximum slab, or the column axis has exactly one minimum slab and one maximum slab, or the individual-extremum count is exactly four. Product saturation, actual slab order and the proved crossed-pattern classification exhaust the alternatives.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.crossed_equality_four`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityCrossed.equality_two_slabs_or_four`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityNeutral](MiuraEqualityNeutral.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraEqualityOrder](MiuraEqualityOrder.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabSigns](MiuraSlabSigns.md)
