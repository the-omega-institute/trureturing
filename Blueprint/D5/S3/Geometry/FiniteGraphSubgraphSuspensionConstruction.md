# Subgraph suspension construction

## Abstract

The finite star gadget, exact face cover, and coordinate contractions.

**Definition 1.1 (Maximal independent sets).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.MaxIndependent`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.MaxIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a finite simple graph H, MaxIndependent(H) consists of its inclusion-maximal independent finite vertex sets, rather than just the sets of maximum cardinality.

**Theorem 1.2 (Independent extension).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.maximal_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.maximal_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Every independent finite vertex set of a finite graph H is contained in a maximal independent set of H.

**Theorem 1.3 (Isolated vertices are retained).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.isolated_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.isolated_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Every isolated H-vertex belongs to every maximal independent set of H. Thus extending H to the ambient vertex set adds no apex adjacency outside its original vertices.

**Definition 1.4 (The literal star gadget).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.suspensionGraph`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.suspensionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For finite graphs H and G on V, the gadget has vertices V plus a hub plus one apex for each maximal H-independent set M. On old vertices it retains exactly the G-edges absent from H. The hub is adjacent to every apex and no old vertex. Distinct apices have no edge; the apex of M is adjacent to exactly the old vertices outside M. The homology theorem assumes H is an arbitrary edge subgraph of G and does not require inducedness.

**Theorem 1.5 (No outside apex neighbors).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.subgraph_apex_off_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.subgraph_apex_off_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every Mathlib subgraph H of G, every maximal independent set of its spanning graph, and every old vertex outside H.verts, that old vertex has no edge to the corresponding gadget apex.

**Definition 1.6 (Closed independence stars).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.closedStar`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.closedStar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For each gadget vertex a, the closed star consists of nonempty independent faces whose vertices are all nonadjacent to a. Adjoining a preserves every such face.

**Definition 1.7 (The hub star).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starA`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A is the closed star of the hub. Its faces contain no apex, and adjoining the hub contracts it.

**Definition 1.8 (The independent apex star cluster).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starB`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

B is the union of the closed stars of all the mutually nonadjacent apices. The finite union is defined by the actual faces of those stars.

**Theorem 1.9 (The literal face cover).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.cover_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.cover_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every pair of finite graphs G,H on V, the actual gadget independence complex equals A union B. A face containing an apex belongs to that apex star, and a face containing none belongs to the hub star.

**Theorem 1.10 (Exact old intersection).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.intersection_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.intersection_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every H less than or equal to G, A intersect B equals the old-vertex embedding of the actual independence complex of G. Both retained edges in G minus H and H-edges remain constraints in this intersection. Arbitrary noninduced H is included.

**Definition 1.11 (Total apex mass).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.mass`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.mass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every real gadget coordinate vector x, mass(x) is the finite sum of the coordinates at all apices.

**Definition 1.12 (Mass outside one apex star).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.bad`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.bad` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For each maximal H-independent set M, b_M(x) is the hub coordinate plus the sum of all old coordinates outside M.

**Definition 1.13 (A continuous finite minimum).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.delta`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.delta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Delta(x) is the minimum of b_M(x) over the nonempty finite family of maximal H-independent sets. Continuity follows from finite minima; the maps never select an argmin. For nonnegative vectors delta vanishes exactly when the hub and every old coordinate outside some M vanish.

**Theorem 1.14 (The cluster zero set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starB_realization_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starB_realization_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every real gadget coordinate vector x, membership in the realized apex star cluster is equivalent to membership in the actual gadget independence realization together with delta(x)=0.

**Definition 1.15 (The fixed threshold).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.epsilon`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.epsilon` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Write N for the total number of gadget vertices. The fixed threshold is epsilon=1/(4(N+1)); it is strictly positive and N epsilon is strictly less than one quarter.

**Definition 1.16 (The first actual open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.U`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Inside the actual gadget independence realization X, U is the set of points with total apex mass strictly less than one half.

**Definition 1.17 (The second actual open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.O`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.O` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Inside X, O is the set where delta is strictly less than epsilon. These sets are open in the actual subspace topology.

**Theorem 1.18 (An actual open cover).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.open_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.open_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every pair of finite graphs G,H, U union O is all of X. Positive apex mass forces b_M=0 at an occupied apex, and hence delta=0.

**Theorem 1.19 (Contraction of the first open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.contractible_U`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.contractible_U` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Erase all apex coordinates and normalize, then interpolate to the hub. Both stages remain in U and in the actual independence realization. This constructs contractibility of U for all finite G,H.

**Theorem 1.20 (Contraction of the closed star cluster).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.contractible_starB`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.contractible_starB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Apply the fixed epsilon cutoff and normalize. Then interpolate to the compatible apex probability vector with unnormalized weights max(epsilon-b_M,0), and finally to a fixed apex. The fixed cutoff denominator exceeds three quarters. At least one apex weight is at least epsilon-delta, hence strictly positive in O. The support tests preserve actual independence and delta=0 throughout the contraction on B. This constructs contractibility of the actual finite apex star cluster.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.MaxIndependent`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.O`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.U`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.bad`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.closedStar`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.contractible_U`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.contractible_starB`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.cover_faces`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.delta`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.epsilon`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.intersection_faces`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.isolated_mem`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.mass`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.maximal_extension`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.open_cover`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starA`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starB`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.starB_realization_iff`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.subgraph_apex_off_vertices`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction.suspensionGraph`
- Dependency: [D5/S3/Geometry/FiniteCoordinateTruncation](FiniteCoordinateTruncation.md)
