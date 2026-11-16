# Lozin moves as local star suspensions

## Abstract

Lozin moves as local star suspensions

**Definition 1.1 (The local star).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.starSubgraph`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.starSubgraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The chosen center and its nonempty selected neighbor set define the local star subgraph. Edges between leaves remain ambient edges.

**Definition 1.2 (The literal Lozin replacement).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspension`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspension` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A partition of the center neighborhood into disjoint sets Y and Z replaces the center by a four-vertex path, with the endpoints attached to Y and Z respectively.

**Definition 1.3 (Identification with the star gadget).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspensionIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspensionIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

When Y is nonempty and Y,Z partition the center neighborhood, the literal replacement is isomorphic to the arbitrary-subgraph suspension of the local star.

**Definition 1.4 (Reduced singular homology transport).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspensionReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspensionReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For finite graphs and every q at least one, the replacement shifts actual reduced integral singular homology by one degree. The graph operation, rather than a homology premise, supplies the transport.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspension`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspensionIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.lozinSuspensionReducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.starSubgraph`
- Dependency: [D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching](EdgeMatching.md)
