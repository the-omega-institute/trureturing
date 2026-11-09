# Edge and matching suspension moves

## Abstract

Edge and matching suspension moves

**Definition 1.1 (Three fresh vertices).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivision`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivision` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The literal triple subdivision deletes only the chosen edge and replaces it by a path with three fresh internal vertices, retaining every other old edge.

**Definition 1.2 (Identification with the edge gadget).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivisionIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivisionIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The actual triple-subdivision graph is isomorphic to the local arbitrary-subgraph suspension gadget of the chosen edge.

**Definition 1.3 (The integral homology shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivisionReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivisionReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a nonempty finite graph, an actual chosen edge and every q at least one, triple subdivision identifies reduced integral singular homology in degree q+1 with that of the original independence realization in degree q.

**Definition 1.4 (The matching gadget).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.crossingSuspension`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.crossingSuspension` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Two disjoint chosen edges are replaced using a new hub and four quadrant vertices. Their endpoints may have extra ambient edges.

**Definition 1.5 (The matching homology shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.crossingSuspensionReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.crossingSuspensionReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every injective choice of the four endpoints of two edges and every q at least one, the actual matching gadget gives the same one-degree reduced integral singular homology shift.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.crossingSuspension`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.crossingSuspensionReducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivision`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivisionIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.tripleSubdivisionReducedHomologyIso`
- Dependency: [D5/S3/Geometry/FiniteGraphSuspensionMoves/Models](Models.md)
