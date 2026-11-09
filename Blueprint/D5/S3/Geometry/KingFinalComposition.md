# Integral torsion in an induced king-grid graph

## Abstract

Integral torsion in an induced king-grid graph

**Definition 1.1 (The same finite endpoint).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.replayToRouteBaseIso`

*Formalization.* `D5/S3/Geometry/KingFinalComposition.replayToRouteBaseIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Literal natural labels and adjacency identify the forty-move endpoint with the base graph of the 178 prescribed routes.

**Definition 1.2 (The total suspension transport).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.selectedReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/KingFinalComposition.selectedReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The forty moves and 31286 prescribed triple subdivisions give an isomorphism from the selected independence realization in reduced degree q+31326 to the actual seed realization in degree q, for q at least one.

**Definition 1.3 (Ordinary integral degree 31327).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.selectedSingularHomologyIso`

*Formalization.* `D5/S3/Geometry/KingFinalComposition.selectedSingularHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The actual singular seed comparison and positive-degree reduced-to-ordinary isomorphisms identify ordinary integral singular homology in degree 31327 of the selected realization with ordinary integral H1 of the seed realization.

**Theorem 1.4 (A nonzero class killed by two).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.selectedSingularClass_nonzero_killed_by_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFinalComposition.selectedSingularClass_nonzero_killed_by_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The original seed cycle transports to a nonzero class of ordinary integral singular homology in degree 31327 of the actual selected induced graph. Twice this class is zero.

**Theorem 1.5 (The sphere-bouquet obstruction).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.selected_not_sourceSP`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFinalComposition.selected_not_sourceSP` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The selected finite realization is compact. The compact sourceSP torsion theorem, with arbitrary sphere indexing families, dimensions including zero and arbitrary basepoints in the ordinary quotient wedge topology, contradicts its nonzero positive-degree integral torsion.

**Theorem 1.6 (The hereditary counterexample).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.rectangle_not_sourceSW`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFinalComposition.rectangle_not_sourceSW` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The selected set is nonempty, so its failure of sourceSP refutes sourceSW for the strong product of paths on 9337 and 9061 vertices. The formal sourceSW convention excludes empty induced sets; the source paper leaves its vertexless convention unspecified. This nonempty obstruction is independent of that convention.

**Theorem 1.7 (The universal hereditary extension is false).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.result`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFinalComposition.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The claim quantifies over every pair of positive path orders and every nonempty induced set, with the original sourceSP alternatives. The actual selected nonempty graph refutes that universal statement. The claim and result retain their arbitrary sphere-index universe parameter. The utility header separately enrolls their closed universe-zero instance as utilityClaim and utilityRefutation; that administrative enrollment adds no mathematical contribution and does not establish the full arbitrary-family scope, which is supplied by the unchanged polymorphic result.

**Theorem 1.8 (Question 32).**

Lean statement: `D5/S3/Geometry/KingFinalComposition.question32_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/KingFinalComposition.question32_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The actual selected induced graph has 93999 vertices and 94036 edges and fails sourceSP. It gives the hereditary obstruction asked in Question 32 of Carnero Bravo. Question 35 concerns the entire rectangle and has a different conclusion. The seed and suspension mechanisms retain their classical attribution; no priority or exhaustive later-literature claim follows from these mathematical statements.

## References

- Truth anchor: `D5/S3/Geometry/KingFinalComposition.question32_counterexample`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.rectangle_not_sourceSW`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.replayToRouteBaseIso`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.result`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.selectedReducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.selectedSingularClass_nonzero_killed_by_two`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.selectedSingularHomologyIso`
- Truth anchor: `D5/S3/Geometry/KingFinalComposition.selected_not_sourceSP`
- Dependency: [D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes](../Combinatorics/Graph/Products/CarneroBravoKingRoutes.md)
- Dependency: [D5/S3/Geometry/FiniteGraphSuspensionMoves](FiniteGraphSuspensionMoves.md)
- Dependency: [D5/S3/Geometry/IndependenceComplexTorsionSeedSingular](IndependenceComplexTorsionSeedSingular.md)
- Dependency: [D5/S3/Geometry/KingFiniteReplay](KingFiniteReplay.md)
- Dependency: [D5/S3/Geometry/PrescribedSubdivisionHomology](PrescribedSubdivisionHomology.md)
- Dependency: [D5/S3/Geometry/SphereBouquetHomology](SphereBouquetHomology.md)
