# Existence of minimum and maximum slab types

## Abstract

Frozen cuts force both nonneutral signs among actual occupied slabs.

**Theorem 1.1 (A minimum-type slab exists).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabSigns.minimum_row_slab_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabSigns.minimum_row_slab_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual unit-edge array with at least two rows, at least one column and an unoccupied row, its canonical minimum-type row slab family is nonempty. If the earliest positive frozen slope has no earlier frozen row, the top occupied slab is minimum type. Otherwise the last preceding negative frozen row and the earliest positive frozen row enclose a minimum-type occupied slab. If there is no positive frozen slope, the last frozen row has negative slope and the bottom slab is minimum type.

**Theorem 1.2 (A maximum-type slab exists).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabSigns.maximum_row_slab_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabSigns.maximum_row_slab_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same actual-array assumptions, the canonical maximum-type row slab family is nonempty. Negation preserves the occupied interval family and exchanges the minimum and maximum outward cut signs.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabSigns.maximum_row_slab_exists`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabSigns.minimum_row_slab_exists`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabClassification](MiuraSlabClassification.md)
