# Exact signed column deletion identities

## Abstract

Exact signed column deletion identities.

**Theorem 1.1 (A frozen column after a deletion to its left).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.frozen_after_left_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.frozen_after_left_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual unit-edge integer height function, a nonempty row axis, frozen columns j and k, and j<k, deleting j leaves column k-1 frozen in the actual contracted array. The uniform signed edge equations also cover consecutive j and k.

**Theorem 1.2 (A frozen column after a deletion to its right).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.frozen_after_right_deletion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.frozen_after_right_deletion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same height and nonempty-row hypotheses, if k<j, deleting frozen column j leaves frozen column k at its original index. At the seam, the height correction equals the genuine uniform slope.

**Theorem 1.3 (Overlapping deletions give equal functions).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.adjacent_deletions_equal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.adjacent_deletions_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual unit-edge height function with at least one row, if j and k are frozen and j+1=k, contracting at j and contracting at k give equal functions on the same rectangle with one fewer column. Their signed slopes agree; every height, including the unchanged origin height, agrees.

**Theorem 1.4 (Two signed deletions commute with index transport).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.separated_deletions_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.separated_deletions_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For frozen j<k in an actual unit-edge array with a nonempty row axis, contracting j and then k-1 equals contracting k and then j. Each second frozen equation is supplied by the survival identities. The equality concerns all integer values, including both signed corrections, on the rectangle with two fewer columns.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.adjacent_deletions_equal`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.frozen_after_left_deletion`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.frozen_after_right_deletion`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraCanonicalColumns.separated_deletions_commute`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCoreNormal](MiuraCoreNormal.md)
