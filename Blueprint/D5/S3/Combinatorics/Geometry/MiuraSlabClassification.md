# Classification by actual boundary cuts

## Abstract

Actual maximal occupied intervals have minimum, maximum or neutral type.

**Theorem 1.1 (The three actual types partition the slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.row_slab_card_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.row_slab_card_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same actual unit-edge, dimension and frozen-row assumptions, the total row slab cardinality equals the sum of the minimum, maximum and neutral row slab cardinalities. A proper interval cannot have both unit outward signs, and an equal-cut internal interval cannot also have a common nonzero outward sign.

**Theorem 1.2 (Outward signs from actual cuts).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.outward_of_cuts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.outward_of_cuts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every existing edge above the first row and below the last row of a coordinate interval has the same outward height increment, then every existing vertical edge leaving that interval has that increment. Adjacency forces it to lie on one of those two boundary cuts; physical boundaries contribute no edge.

**Theorem 1.3 (Exhaustive slab types).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.row_slab_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.row_slab_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-edge integer height array with at least two rows, at least one column and at least one unoccupied row, each maximal occupied row interval is a minimum, maximum or neutral row slab as defined by its actual boundary edges. The frozen row assumption excludes a whole-axis occupied interval. The immediately adjacent outside rows are unoccupied by maximality; physical boundary occupancy makes these rows internal, and the frozen-cut theorem supplies their uniform unit signs. Opposite cut signs give a minimum or maximum type, equal signs give neutral type, and a physical end omits its absent cut.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.outward_of_cuts`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.row_slab_card_partition`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabClassification.row_slab_classification`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabFrozen](MiuraSlabFrozen.md)
