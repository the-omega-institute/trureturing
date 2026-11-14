# Real bundles on actual continuously varying subspaces

## Abstract

Real bundles on actual continuously varying subspaces

**Definition 1.1 (Actual local linear coordinates).**

Lean statement: `D5/S3/Geometry/ContinuousRangeBundle.Chart`

*Formalization.* `D5/S3/Geometry/ContinuousRangeBundle.Chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A chart consists of an open base set, forward maps into the actual submodules and backward maps from the ambient Euclidean space. Both map families are continuous on the open set. Both inverse laws hold on that set. This is constructed local data, not an additional premise of the projection-range theorem.

**Theorem 1.2 (Projection continuity constructs charts).**

Lean statement: `D5/S3/Geometry/ContinuousRangeBundle.exists_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ContinuousRangeBundle.exists_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a family of actual real submodules of fixed finite rank, continuity of their orthogonal projections constructs a chart neighborhood at every base point. Project a fixed basis of the reference fiber. Injectivity is open. The projected maps remain injective on a neighborhood; equality of dimensions gives equality with the whole actual range. Their invertible Gram operators give continuous coordinate inverses.

**Definition 1.3 (The genuine real vector prebundle).**

Lean statement: `D5/S3/Geometry/ContinuousRangeBundle.prebundle`

*Formalization.* `D5/S3/Geometry/ContinuousRangeBundle.prebundle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All constructed local linear coordinates form a VectorPrebundle on the actual submodules. The overlap map is the second chart coordinate map composed with the first chart reconstruction map, and is continuous in operator norm. The standard VectorPrebundle construction provides the real vector bundle.

**Theorem 1.4 (Exactly the ambient range graph topology).**

Lean statement: `D5/S3/Geometry/ContinuousRangeBundle.topology_eq_induced`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ContinuousRangeBundle.topology_eq_induced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generated bundle topology equals the topology induced by the actual inclusion into X times H. Local reconstruction proves continuity of the ambient inclusion, and local coordinates prove continuity of the inverse from the range graph. This is equality of total topologies, not only pointwise agreement of fiber topologies.

## References

- Truth anchor: `D5/S3/Geometry/ContinuousRangeBundle.Chart`
- Truth anchor: `D5/S3/Geometry/ContinuousRangeBundle.exists_chart`
- Truth anchor: `D5/S3/Geometry/ContinuousRangeBundle.prebundle`
- Truth anchor: `D5/S3/Geometry/ContinuousRangeBundle.topology_eq_induced`
