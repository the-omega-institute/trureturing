# Finite local subgraphs and maximal independent sets

## Abstract

Finite local subgraphs and maximal independent sets

**Definition 1.1 (An embedded edge subgraph).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.embeddedIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.embeddedIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

An injective map of a finite model graph into a finite graph defines the subgraph containing exactly the model edges. The model is isomorphic to that local subgraph. Extra ambient edges between its vertices are retained outside the subgraph.

**Theorem 1.2 (Apex complement membership).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.embedded_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.embedded_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For each maximal independent set of the model, membership outside its transported apex set is exactly membership in the image of the model complement.

**Definition 1.3 (One edge).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.edgeMaxEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.edgeMaxEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The single edge has exactly two maximal independent sets, the singleton endpoints.

**Definition 1.4 (Two disjoint edges).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.quadrantMaxEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.quadrantMaxEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The two-edge matching has exactly four maximal independent sets, choosing one endpoint on each edge. Ambient cross edges do not enter this model.

**Definition 1.5 (A nonempty star).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.starMaxEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.starMaxEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A star with a finite nonempty leaf set has exactly two maximal independent sets: its center and its entire leaf set.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.edgeMaxEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.embeddedIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.embedded_complement`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.quadrantMaxEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Models.starMaxEquiv`
- Dependency: [D5/S3/Geometry/FiniteGraphSubgraphSuspension](../FiniteGraphSubgraphSuspension.md)
