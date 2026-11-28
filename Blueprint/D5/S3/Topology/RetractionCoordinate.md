# Retractions of the coloured tetrahedral regions

## Abstract

Retractions of the coloured tetrahedral regions

**Theorem 1.1 (Ordinary path coordinates of the two-cut retraction).**

Lean statement: `D5/S3/Topology/RetractionCoordinate.retractionHeight_of_rank_retraction`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RetractionCoordinate.retractionHeight_of_rank_retraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

At each of three ordinary subdivisions, take the sum of the least and greatest coordinates in the underlying face. For an actual retraction in the two-cut collar, this coordinate equals the height computed from the corresponding tetrahedral row. The calculation respects repeated images under the rank map.

**Theorem 1.2 (The main region admits a single contiguity chain).**

Lean statement: `D5/S3/Topology/RetractionCoordinate.main_retraction_glued`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RetractionCoordinate.main_retraction_glued` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A proper rank colouring supplies a compatible oriented interval chart on each old edge. A main vertex supported on one old vertex keeps its endpoint value in every incident chart. These endpoint agreements glue the relative interval interpolation from the two-cut retraction to the map obtained by halving the chamber heights.

**Theorem 1.3 (The main region factors through the finer edge charts).**

Lean statement: `D5/S3/Topology/RetractionCoordinate.main_retraction_glued_refined`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RetractionCoordinate.main_retraction_glued_refined` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The full integer heights give a simplicial map to the fourth subdivision. Choosing a vertex of each face gives the comparison to the third subdivision. The relative contiguity comparison fixes the old endpoints.

**Theorem 1.4 (Each extra component retracts into one subdivided edge).**

Lean statement: `D5/S3/Topology/RetractionCoordinate.extra_retraction_in_subdivided_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RetractionCoordinate.extra_retraction_in_subdivided_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A proper rank colouring is injective on each old face. The two opposite ranks present in every extra carrier select a single edge throughout a connected component. The opposite two-cut retraction lands in the third subdivision of that edge.

## References

- Truth anchor: `D5/S3/Topology/RetractionCoordinate.extra_retraction_in_subdivided_edge`
- Truth anchor: `D5/S3/Topology/RetractionCoordinate.main_retraction_glued`
- Truth anchor: `D5/S3/Topology/RetractionCoordinate.main_retraction_glued_refined`
- Truth anchor: `D5/S3/Topology/RetractionCoordinate.retractionHeight_of_rank_retraction`
- Dependency: [D5/S3/Topology/IntervalSubdivisionCoordinates](IntervalSubdivisionCoordinates.md)
- Dependency: [D5/S3/Topology/OrdinaryCollarRetraction](OrdinaryCollarRetraction.md)
- Dependency: [D5/S3/Topology/OrdinaryTetrahedronCollar](OrdinaryTetrahedronCollar.md)
- Dependency: [D5/S3/Topology/RankColouredTetrahedron](RankColouredTetrahedron.md)
- Dependency: [D5/S3/Topology/RelativeIntervalChartGluing](RelativeIntervalChartGluing.md)
