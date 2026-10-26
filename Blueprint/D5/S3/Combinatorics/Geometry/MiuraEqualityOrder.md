# MiuraEqualityOrder

## Abstract

Actual-array geometric equality for the original Miura residual class.

**Theorem 1.1 (minimum slab between maximum slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.minimum_slab_between_maximum_slabs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.minimum_slab_between_maximum_slabs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array with at least two rows and at least one column, any specified maximum row slabs A and B with the last row of A strictly before the first row of B have a minimum row slab I strictly between them: the first row of I is after the last row of A and the last row of I is before the first row of B. Its signed transition is selected from genuinely unoccupied rows, using the existing frozen-cut suppliers.

**Theorem 1.2 (boundary maximum slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.boundary_maximum_slabs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.boundary_maximum_slabs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array with at least two rows, at least one column and a genuinely unoccupied row, if there is exactly one minimum row slab and at least two maximum row slabs, then maximum row slabs contain the physical first and last rows, respectively. The intervening minimum slab between two maxima is internal, so the unique minimum slab cannot be a boundary slab.

**Theorem 1.3 (one minimum slab maximum card le two).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.one_minimum_slab_maximum_card_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.one_minimum_slab_maximum_card_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual integer unit-edge height array with at least two rows and at least one column, exactly one minimum row slab implies at most two maximum row slabs. Distinct maximum slabs must straddle that unique minimum slab; their position relative to it gives an injection into a two-element type.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.boundary_maximum_slabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.minimum_slab_between_maximum_slabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraEqualityOrder.one_minimum_slab_maximum_card_le_two`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabClassification](MiuraSlabClassification.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabRunBound](MiuraSlabRunBound.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabSigns](MiuraSlabSigns.md)
