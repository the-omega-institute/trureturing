# Simultaneous prescribed triple subdivisions

## Abstract

Simultaneous prescribed triple subdivisions

**Definition 1.1 (The complete endpoint graph).**

Lean statement: `D5/S3/Geometry/PrescribedSubdivisionHomology.baseGraph`

*Formalization.* `D5/S3/Geometry/PrescribedSubdivisionHomology.baseGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Every supplied unordered endpoint pair is an edge of the base graph. All original vertices, including isolated vertices, are retained.

**Theorem 1.2 (The current terminal edge).**

Lean statement: `D5/S3/Geometry/PrescribedSubdivisionHomology.tip_adjacent`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/PrescribedSubdivisionHomology.tip_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A partial path with multiplicity zero retains the original edge; a positive path has its terminal internal vertex adjacent to the original right endpoint.

**Definition 1.3 (One actual subdivision step).**

Lean statement: `D5/S3/Geometry/PrescribedSubdivisionHomology.stepIso`

*Formalization.* `D5/S3/Geometry/PrescribedSubdivisionHomology.stepIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Increasing one multiplicity by one identifies the new partial graph with a literal triple subdivision of its current terminal edge. Injectivity of unordered endpoint pairs handles the zero-stage edge deletion.

**Definition 1.4 (The final path carrier).**

Lean statement: `D5/S3/Geometry/PrescribedSubdivisionHomology.positiveIso`

*Formalization.* `D5/S3/Geometry/PrescribedSubdivisionHomology.positiveIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

At the prescribed positive multiplicities, the partial graph is isomorphic to the actual prescribed-subdivision graph on original vertices and indexed internal path vertices.

**Definition 1.5 (The total homology shift).**

Lean statement: `D5/S3/Geometry/PrescribedSubdivisionHomology.reducedHomologyIsoOfAdjacency`

*Formalization.* `D5/S3/Geometry/PrescribedSubdivisionHomology.reducedHomologyIsoOfAdjacency` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For finite original vertex and edge types, injective unordered endpoint pairs, an exact endpoint adjacency inventory for G and q at least one, the actual prescribed graph has reduced integral singular homology in degree q plus the sum of multiplicities isomorphic to that of G in degree q. Well-founded recursion on the total multiplicity proves the iteration without a nested expanded carrier.

## References

- Truth anchor: `D5/S3/Geometry/PrescribedSubdivisionHomology.baseGraph`
- Truth anchor: `D5/S3/Geometry/PrescribedSubdivisionHomology.positiveIso`
- Truth anchor: `D5/S3/Geometry/PrescribedSubdivisionHomology.reducedHomologyIsoOfAdjacency`
- Truth anchor: `D5/S3/Geometry/PrescribedSubdivisionHomology.stepIso`
- Truth anchor: `D5/S3/Geometry/PrescribedSubdivisionHomology.tip_adjacent`
- Dependency: [D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision](../Combinatorics/Graph/Products/PrescribedSubdivision.md)
- Dependency: [D5/S3/Geometry/FiniteGraphSuspensionMoves](FiniteGraphSuspensionMoves.md)
