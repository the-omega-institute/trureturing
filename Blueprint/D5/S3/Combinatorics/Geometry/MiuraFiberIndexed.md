# All prescribed frozen-line insertions in one actual array

## Abstract

Indexed actual frozen-line expansion.

**Definition 1.1 (Cumulative surviving coordinates).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.columnPosition`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.columnPosition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An original column j has final coordinate j plus the sum of all prescribed extra copies at original columns k at or before j. This is a natural coordinate in the expanded rectangle.

**Definition 1.2 (Exact individual extremum transport).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.ColumnExtremaExpansion`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.ColumnExtremaExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each actual cell of the expanded function, being a strict full-neighbour minimum is equivalent to coming from an original minimum with unchanged row and the cumulative column coordinate. The same equivalence holds separately for every maximum. The predicates concern actual integer height functions on the two rectangles.

**Theorem 1.3 (Simultaneous realization of every finite insertion vector).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.indexed_column_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.indexed_column_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given an actual normalized residual array with a nonempty row axis, prescribe a natural number of extra copies at each original column, supported only on genuinely frozen columns. A single actual normalized unit-edge array exists at width n plus the sum of all those coordinates. It has the same exact minimum and maximum counts and original common-side exclusion, reduces to the original function through legal frozen-pair deletions, and satisfies both exact individual extremum transport equivalences. Induction on the total number of insertions preserves the ordered coordinates and proves frozen availability at every prescribed original line. This result does not identify every array in a joint core fiber with such a vector.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.ColumnExtremaExpansion`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.columnPosition`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberIndexed.indexed_column_expansion`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreStretch](MiuraCoreStretch.md)
