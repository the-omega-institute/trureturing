# Arbitrary subgraph star suspension

## Abstract

An arbitrary-subgraph star gadget and its actual reduced singular integral homology shift.

**Definition 1.1 (Maximal independent sets).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.MaxIndependent`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.MaxIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a finite simple graph H, MaxIndependent(H) consists of its inclusion-maximal independent finite vertex sets, rather than just the sets of maximum cardinality.

**Theorem 1.2 (Independent extension).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.maximal_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.maximal_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Every independent finite vertex set of a finite graph H is contained in a maximal independent set of H.

**Theorem 1.3 (Isolated vertices are retained).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.isolated_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.isolated_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Every isolated H-vertex belongs to every maximal independent set of H. Thus extending H to the ambient vertex set adds no apex adjacency outside its original vertices.

**Definition 1.4 (The literal star gadget).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.suspensionGraph`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.suspensionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For finite graphs H and G on V, the gadget has vertices V plus a hub plus one apex for each maximal H-independent set M. On old vertices it retains exactly the G-edges absent from H. The hub is adjacent to every apex and no old vertex. Distinct apices have no edge; the apex of M is adjacent to exactly the old vertices outside M. The homology theorem assumes H is an arbitrary edge subgraph of G and does not require inducedness.

**Theorem 1.5 (No outside apex neighbors).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraph_apex_off_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraph_apex_off_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every Mathlib subgraph H of G, every maximal independent set of its spanning graph, and every old vertex outside H.verts, that old vertex has no edge to the corresponding gadget apex.

**Definition 1.6 (Closed independence stars).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.closedStar`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.closedStar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For each gadget vertex a, the closed star consists of nonempty independent faces whose vertices are all nonadjacent to a. Adjoining a preserves every such face.

**Definition 1.7 (The hub star).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starA`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A is the closed star of the hub. Its faces contain no apex, and adjoining the hub contracts it.

**Definition 1.8 (The independent apex star cluster).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starB`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

B is the union of the closed stars of all the mutually nonadjacent apices. The finite union is defined by the actual faces of those stars.

**Theorem 1.9 (The literal face cover).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.cover_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.cover_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every pair of finite graphs G,H on V, the actual gadget independence complex equals A union B. A face containing an apex belongs to that apex star, and a face containing none belongs to the hub star.

**Theorem 1.10 (Exact old intersection).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.intersection_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.intersection_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every H less than or equal to G, A intersect B equals the old-vertex embedding of the actual independence complex of G. Both retained edges in G minus H and H-edges remain constraints in this intersection. Arbitrary noninduced H is included.

**Definition 1.11 (Total apex mass).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.mass`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.mass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every real gadget coordinate vector x, mass(x) is the finite sum of the coordinates at all apices.

**Definition 1.12 (Mass outside one apex star).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.bad`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.bad` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For each maximal H-independent set M, b_M(x) is the hub coordinate plus the sum of all old coordinates outside M.

**Definition 1.13 (A continuous finite minimum).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.delta`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Delta(x) is the minimum of b_M(x) over the nonempty finite family of maximal H-independent sets. Continuity follows from finite minima; the maps never select an argmin. For nonnegative vectors delta vanishes exactly when the hub and every old coordinate outside some M vanish.

**Theorem 1.14 (The cluster zero set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starB_realization_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starB_realization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every real gadget coordinate vector x, membership in the realized apex star cluster is equivalent to membership in the actual gadget independence realization together with delta(x)=0.

**Definition 1.15 (The fixed threshold).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.epsilon`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Write N for the total number of gadget vertices. The fixed threshold is epsilon=1/(4(N+1)); it is strictly positive and N epsilon is strictly less than one quarter.

**Definition 1.16 (The first actual open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.U`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Inside the actual gadget independence realization X, U is the set of points with total apex mass strictly less than one half.

**Definition 1.17 (The second actual open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.O`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.O` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Inside X, O is the set where delta is strictly less than epsilon. These sets are open in the actual subspace topology.

**Theorem 1.18 (An actual open cover).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.open_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.open_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every pair of finite graphs G,H, U union O is all of X. Positive apex mass forces b_M=0 at an occupied apex, and hence delta=0.

**Theorem 1.19 (Contraction of the first open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_U`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_U` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Erase all apex coordinates and normalize, then interpolate to the hub. Both stages remain in U and in the actual independence realization. This constructs contractibility of U for all finite G,H.

**Theorem 1.20 (Contraction of the closed star cluster).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_starB`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_starB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Apply the fixed epsilon cutoff and normalize. Then interpolate to the compatible apex probability vector with unnormalized weights max(epsilon-b_M,0), and finally to a fixed apex. The fixed cutoff denominator exceeds three quarters. At least one apex weight is at least epsilon-delta, hence strictly positive in O. The support tests preserve actual independence and delta=0 throughout the contraction on B. This constructs contractibility of the actual finite apex star cluster.

**Definition 1.21 (A variable-cutoff neighborhood retraction).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.neighborhoodRetraction`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.neighborhoodRetraction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

On O, apply the variable cutoff delta(x) to every coordinate and normalize. The coordinate sum exceeds three quarters, all support shrinks, and a minimizing b_M has its forbidden coordinates killed. The resulting continuous map lands in B. It fixes B pointwise because delta=0 there.

**Definition 1.22 (The actual neighborhood equivalence).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.neighborhoodEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.neighborhoodEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The variable-cutoff retraction and the inclusion of B in O are homotopy inverse. Straight interpolation is supported in the original independent face and stays in O by the b_M bound. The other composite is exactly the identity on B.

**Theorem 1.23 (Contractibility of the second open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_O`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_O` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The constructed equivalence with the actual contractible apex star cluster makes O contractible. No homological vanishing assumption is supplied.

**Definition 1.24 (The actual open intersection).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.intersectionEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.intersectionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every H less than or equal to G, the old epsilon cutoff and normalization map U intersect O to the actual old independence realization. Its denominator exceeds one quarter. Edges of H are excluded by a maximal independent set; edges retained from G minus H are excluded by the original gadget support. Inclusion on old coordinates is the inverse up to the two displayed straight homotopies.

**Definition 1.25 (Local and spanning maximal sets).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localMaxEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localMaxEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every subgraph H of G, restriction to H.verts bijects maximal independent sets of the spanning graph with those of the local graph. The inverse adjoins all outside vertices, which are isolated in the spanning graph.

**Definition 1.26 (The local vertex convention).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSuspensionGraph`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSuspensionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The literal local gadget keeps old vertices of G and retains every G-edge absent from H. An apex indexed by a maximal independent set of the local H-graph is adjacent to exactly its complement inside H.verts, together with the hub. No induced-subgraph assumption is imposed.

**Definition 1.27 (Exact gadget identification).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.spanningLocalIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.spanningLocalIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every subgraph H of G, the maximal-independent-set bijection gives a graph isomorphism between the spanning and local gadgets. It fixes all old vertices and the hub and preserves all retained G-edges.

**Definition 1.28 (The integral singular homology shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.reducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.reducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty finite vertex type V, every pair of simple graphs H less than or equal to G on V, and every natural q at least one, the actual reduced singular homology with integral coefficients of the gadget independence realization in degree q+1 is isomorphic to that of the actual G-independence realization in degree q. The proof applies the existing open-cover reduced Mayer-Vietoris connecting isomorphism to U and O, then homotopy invariance to the constructed intersection equivalence. It assumes no homology shift, homotopy equivalence, retraction or quasi-isomorphism.

**Definition 1.29 (Arbitrary Mathlib subgraphs).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraphReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraphReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty finite G, every possibly noninduced Mathlib subgraph H of G, and every q at least one, the spanning version of the literal gadget shifts the actual reduced singular integral homology by one degree.

**Definition 1.30 (The local gadget homology shift).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSubgraphReducedHomologyIso`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSubgraphReducedHomologyIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every nonempty finite G, every arbitrary possibly noninduced subgraph H, every finite instance on H.verts, and every natural q at least one, the actual local gadget independence realization in degree q+1 has reduced singular integral homology isomorphic to that of G in degree q. Transport uses the proved graph isomorphism and the existing coordinate homeomorphism. These results provide core machinery for Carnero Bravo Question 32. They do not settle its hereditary SW statement for all induced subgraphs and arbitrary m; Question 35 about the full rectangle is different. Seed comparison, complete gadget replay, king rotation and the sphere-bouquet torsion obstruction are further obligations. The graph suspension and star-cluster mechanisms belong to the work of Adamaszek, Barmak and Csorba; the explicit coordinate neighborhoods are the construction described here, without a priority claim.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.MaxIndependent`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.O`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.U`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.bad`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.closedStar`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_O`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_U`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.contractible_starB`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.cover_faces`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.delta`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.epsilon`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.intersectionEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.intersection_faces`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.isolated_mem`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localMaxEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSubgraphReducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.localSuspensionGraph`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.mass`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.maximal_extension`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.neighborhoodEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.neighborhoodRetraction`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.open_cover`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.reducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.spanningLocalIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starA`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starB`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.starB_realization_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraphReducedHomologyIso`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.subgraph_apex_off_vertices`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspension.suspensionGraph`
- Dependency: [D5/S3/Geometry/FiniteCoordinateTruncation](FiniteCoordinateTruncation.md)
