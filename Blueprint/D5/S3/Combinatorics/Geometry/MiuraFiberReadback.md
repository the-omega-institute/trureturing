# Injective fixed-core length readback

## Abstract

Read all indexed lengths from actual occupied positions.

**Theorem 1.1 (Every frozen-line coordinate is determined).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraFiberReadback.indexed_column_weights_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraFiberReadback.indexed_column_weights_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an actual unit-edge array with nonempty row axis, at least two columns, and no adjacent genuinely frozen columns. Let two natural extra-copy vectors be supported on its frozen columns. If one actual array has the corresponding total width for each vector and satisfies the exact active-column image relation for each vector, allowing any nonempty expanded row dimension, then the entire two vectors are equal. Each active original column has zero extra copies. The two cumulative-position order embeddings of the finite ordered active-column family have the same range in the actual expanded array, hence agree pointwise by the pinned finite-order theorem. Every inactive core column is frozen and its neighbours are active. Their two coordinate gaps recover its exact extra length. No uniqueness of the joint reduced core and no assumed counting bijection enter this proof.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraFiberReadback.indexed_column_weights_unique`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberIndexed](MiuraFiberIndexed.md)
