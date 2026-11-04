# Slab extrema in unit-edge height arrays

## Abstract

Extrema forced by the boundary signs of actual rectangular intervals.

**Definition 1.1 (Coordinate intervals).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.Interval`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.Interval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coordinate interval consists of two actual finite grid coordinates in increasing order. Its first and last coordinates may be physical endpoints.

**Definition 1.2 (The actual rectangle).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.rectangle`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.rectangle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rectangle is the Cartesian product of the two closed coordinate intervals. Its vertices remain vertices of the original array.

**Definition 1.3 (Vertical boundary signs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.RowOutward`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.RowOutward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every existing adjacent edge from a row in the interval to a row outside it changes the original height by the specified integer. At a physical boundary there is no extra edge.

**Definition 1.4 (Horizontal boundary signs).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.ColOutward`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.ColOutward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every existing adjacent edge from a column in the interval to a column outside it has the specified height change in the same array.

**Theorem 1.5 (Matching minimum types force an ambient minimum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.matching_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.matching_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer unit-edge array and every nonempty row and column interval, if every existing outward vertical and horizontal edge increases height by one, their rectangle contains a strict local minimum of the whole array. A lowest rectangle vertex has higher neighbours inside by the unit-edge law and higher neighbours outside by the two boundary conditions.

**Theorem 1.6 (Matching maximum types force an ambient maximum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.matching_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.matching_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer unit-edge array and every nonempty row and column interval, if every existing outward vertical and horizontal edge decreases height by one, their rectangle contains a strict local maximum of the whole array. This follows by applying the minimum result to the negated actual heights.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.ColOutward`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.Interval`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.RowOutward`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.matching_maximum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.matching_minimum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraSlabExtrema.rectangle`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraStripRigidity](MiuraStripRigidity.md)
