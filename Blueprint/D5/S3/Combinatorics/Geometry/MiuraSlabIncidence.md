# Individual extrema and maximal occupied intervals

## Abstract

Individual extrema and maximal occupied intervals

**Definition 1.1 (Actual row slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.IsRowSlab`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.IsRowSlab` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A slab is a nonempty closed row interval in which every row contains an ambient extremum, and every existing immediately adjacent outside row is unoccupied. This is a maximal consecutive occupied interval of the given array.

**Definition 1.2 (All actual row slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.rowSlabs`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.rowSlabs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set contains precisely the maximal occupied intervals of the original array.

**Theorem 1.3 (Slab uniqueness at a row).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.row_slab_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.row_slab_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two maximal occupied intervals containing the same actual row are equal. An earlier endpoint would put the occupied predecessor of the later endpoint inside the earlier interval, contradicting maximality.

**Definition 1.4 (Minimum row slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.minRowSlabs`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.minRowSlabs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are proper actual row slabs all of whose existing outward edges increase height by one. Proper means that at least one outward row cut exists.

**Definition 1.5 (Maximum row slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.maxRowSlabs`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.maxRowSlabs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are proper actual row slabs all of whose existing outward edges decrease height by one.

**Definition 1.6 (Neutral row slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutralRowSlabs`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutralRowSlabs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are actual row slabs internal to the grid with a common unit downward increment on the two full-width boundary cuts. Both signs are included.

**Definition 1.7 (Individual extremum cells).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.extrema`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.extrema` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite extremum set retains each cell that is an ambient minimum or maximum. It does not identify cells with the same pair of slab endpoints.

**Definition 1.8 (Individual row incidences).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.rowIncidences`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.rowIncidences` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A row incidence is an individual extremum cell whose row belongs to the specified interval.

**Theorem 1.9 (Two distinct row incidences).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_row_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_row_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual neutral row slab of an integer unit-edge array with at least two rows contains at least two distinct extremum cells, one minimum and one maximum.

**Theorem 1.10 (Disjoint neutral row counting).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_rows_individual_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_rows_individual_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-edge array with at least two rows, twice the number of actual neutral row slabs is at most the number of individual extrema contained in their union. Distinct actual slabs have disjoint row sets.

**Definition 1.11 (Transposition of the same array).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.transposeHeight`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.transposeHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transposition swaps the two finite coordinates and keeps the original integer height value. Column slab families are the row slab families of this transposed array.

**Theorem 1.12 (Transposed unit-edge law).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.transpose_isHeight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.transpose_isHeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposing an integer unit-edge height array preserves its unit-edge law.

**Definition 1.13 (Neutral column slabs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutralColSlabs`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutralColSlabs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual neutral column intervals are obtained by transposing the original array and taking its neutral row intervals.

**Theorem 1.14 (Two distinct column incidences).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_col_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_col_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual neutral column slab of an integer unit-edge array with at least two rows contains at least two distinct individual extremum cells.

**Theorem 1.15 (Disjoint neutral column counting).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_cols_individual_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_cols_individual_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the number of actual neutral column slabs is at most the number of individual extrema in their union. The proof transports the forcing argument and preserves distinct original cells.

**Theorem 1.16 (Neutral and nonneutral signs are incompatible).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_not_outward`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_not_outward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If an actual internal interval has equal downward cut increments, it cannot have the same nonzero outward increment on both cuts. The actual top and bottom edge equations would force that outward increment to be zero. The grid must have at least one column.

**Theorem 1.17 (Exact minimum and maximum count).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.extrema_card_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.extrema_card_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every array with at least two rows, the cardinality of its individual extremum set is the sum of the exact minimum and maximum cardinalities from the residual counting definitions. A cell cannot be both kinds of extremum because it has an existing neighbour.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.IsRowSlab`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.extrema`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.extrema_card_split`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.maxRowSlabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.minRowSlabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutralColSlabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutralRowSlabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_col_degree`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_cols_individual_count`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_not_outward`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_row_degree`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.neutral_rows_individual_count`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.rowIncidences`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.rowSlabs`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.row_slab_unique`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.transposeHeight`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabIncidence.transpose_isHeight`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraResidualCount](MiuraResidualCount.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraSlabNeutral](MiuraSlabNeutral.md)
