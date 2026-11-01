# Local subgraphs and homology endpoint

## Abstract

Local arbitrary-subgraph transport and the actual reduced singular integral homology endpoint.

**Definition 1.1 (Local and spanning maximal sets).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localMaxEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localMaxEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every subgraph H of G, restriction to H.verts bijects maximal independent sets of the spanning graph with those of the local graph. The inverse adjoins all outside vertices, which are isolated in the spanning graph.

**Definition 1.2 (The local vertex convention).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSuspensionGraph`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSuspensionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The literal local gadget keeps old vertices of G and retains every G-edge absent from H. An apex indexed by a maximal independent set of the local H-graph is adjacent to exactly its complement inside H.verts, together with the hub. No induced-subgraph assumption is imposed.

**Definition 1.3 (Exact gadget identification).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.spanningLocalIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.spanningLocalIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every subgraph H of G, the maximal-independent-set bijection gives a graph isomorphism between the spanning and local gadgets. It fixes all old vertices and the hub and preserves all retained G-edges.

**Definition 1.4 (The integral singular homology shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.reducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.reducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty finite vertex type V, every pair of simple graphs H less than or equal to G on V, and every natural q at least one, the actual reduced singular homology with integral coefficients of the gadget independence realization in degree q+1 is isomorphic to that of the actual G-independence realization in degree q. The proof applies the existing open-cover reduced Mayer-Vietoris connecting isomorphism to U and O, then homotopy invariance to the constructed intersection equivalence. It assumes no homology shift, homotopy equivalence, retraction or quasi-isomorphism.

**Definition 1.5 (Arbitrary Mathlib subgraphs).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraphReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraphReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty finite G, every possibly noninduced Mathlib subgraph H of G, and every q at least one, the spanning version of the literal gadget shifts the actual reduced singular integral homology by one degree.

**Definition 1.6 (The local gadget homology shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSubgraphReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSubgraphReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty finite G, every arbitrary possibly noninduced subgraph H, every finite instance on H.verts, and every natural q at least one, the actual local gadget independence realization in degree q+1 has reduced singular integral homology isomorphic to that of G in degree q. Transport uses the proved graph isomorphism and the existing coordinate homeomorphism. These results provide core machinery for Carnero Bravo Question 32. They do not settle its hereditary SW statement for all induced subgraphs and arbitrary m; Question 35 about the full rectangle is different. Seed comparison, complete gadget replay, king rotation and the sphere-bouquet torsion obstruction are further obligations. The graph suspension and star-cluster mechanisms belong to the work of Adamaszek, Barmak and Csorba; the explicit coordinate neighborhoods are the construction described here, without a priority claim.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localMaxEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSubgraphReducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSuspensionGraph`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.reducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.spanningLocalIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraphReducedHomologyIso`
- Dependency: [D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction](FiniteGraphSubgraphSuspensionRetraction.md)
