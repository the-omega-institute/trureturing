# Three-segment subdivision of finite multigraphs

## Abstract

Three-segment subdivision of finite multigraphs

**Theorem 1.1 (Subdivision preserves connectivity).**

Lean statement: `D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replace each edge by the path through its two incidence flags. Paths between original vertices lift by traversing these paths, and each new flag vertex has a path to an original vertex.

**Theorem 1.2 (Subdivision preserves the degree-one condition).**

Lean statement: `D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.leafless_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.leafless_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original vertices retain the number of incident flags and each new flag vertex has degree two. The two flags of a loop both contribute.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/LeaflessDynamics/TripleEdgeSubdivision.leafless_iff`
- Dependency: [D5/S3/ConceptDynamics/Coding/EssentialWordRealization](../../../ConceptDynamics/Coding/EssentialWordRealization.md)
