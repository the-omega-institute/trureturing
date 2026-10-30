# Occupied-fiber substitution

## Abstract

Induced heterogeneous substitutions retain precisely the occupied base and selected fibers.

**Definition 1.1 (The occupied base).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.occupiedBase`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.occupiedBase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For a dependent family D over V and any subset T of its sigma type, U consists of exactly those v for which some pair (v,d) lies in T. Empty fibers contribute no occupied base vertices.

**Definition 1.2 (The selected fiber).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.selectedFiber`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.selectedFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For u in U, the selected fiber consists of d in D(u) for which (u,d) lies in T, with the actual membership proof retained.

**Definition 1.3 (Nonempty occupied fibers).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.selectedFiberNonempty`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.selectedFiberNonempty` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The witness defining membership in U supplies a selected fiber vertex. This needs no global assumption that T is nonempty.

**Definition 1.4 (Mutually inverse vertex maps).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.vertexEquiv`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.vertexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

A vertex ((v,d),h) of T maps to ((v, exists d with h),(d,h)). The inverse forgets the occupied-base proof and returns ((v,d),h). The first composite is the identity on T, and the second is the identity on the dependent sum of selected fibers by proof irrelevance. These formulas also apply when T is empty.

**Definition 1.5 (The actual restricted substitution).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.selectedGraph`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.selectedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

Induce G on U, induce each H(u) on the selected d, and form their heterogeneous substitution. Neither source class assumptions nor closure assumptions occur.

**Theorem 1.6 (Exact adjacency transport).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.adjacency_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OccupiedFiberSubstitution.adjacency_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For arbitrary V, dependent fibers D, simple graphs G and H(u), any selected set T and x,y in T, adjacency in the induced original substitution holds if and only if adjacency holds between their split vertices in the selected graph. A base edge remains the same induced base edge. A within-fiber edge keeps its actual endpoints and membership proofs in the induced fiber graph. Conversely each of these two kinds of selected edge forgets to the corresponding original edge.

**Definition 1.7 (The occupied-fiber graph isomorphism).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.graphIso`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.graphIso` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The explicit mutually inverse vertex maps and the proved adjacency equivalence give an actual graph isomorphism from the original substitution induced on T to the substitution of selected induced fibers over U.

**Theorem 1.8 (Equality of mapped independent-face complexes).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.mapped_independence_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OccupiedFiberSubstitution.mapped_independence_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For arbitrary V and dependent fibers D(u), with decidable equality, and arbitrary G,H,T, map the nonempty independent faces of the induced original substitution along the graph isomorphism. The result is exactly the nonempty independent-face complex of the selected graph. In the forward direction, adjacency reflection preserves independence. In the reverse direction, image under the inverse vertex equivalence recovers every selected independent face, and adjacency preservation proves independence of its preimage. Nonemptiness is transported by finite-set image in both directions.

**Definition 1.9 (Homeomorphism of the actual independence realizations).**

Lean statement: `D5/S3/Geometry/OccupiedFiberSubstitution.independenceHomeomorph`

*Formalization.* `D5/S3/Geometry/OccupiedFiberSubstitution.independenceHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every finite base V, finite dependent fibers D(u), simple graphs G and H(u), and arbitrary T in the sigma vertex set, the native finite-coordinate realization of the independence complex of the original substitution induced on T is homeomorphic to that of the selected substitution over U. Apply the existing embedding realization homeomorphism to the explicit graph isomorphism, then transport along the proved equality of mapped independent-face complexes. The adjacency result is thus used in the realization transport. No second coordinate transport construction is needed. Empty T and empty original fibers remain in scope. This exact heterogeneous transport is a local RepoDerived refinement associated with the induced-subgraph description in Carnero Bravo arXiv:2505.06457v2, not an exact theorem attributed to the paper. It supplies an intermediate step for the unsuspended hereditary induction and asserts neither Question 22 nor membership in the stronger SW class.

## References

- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.adjacency_iff`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.graphIso`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.independenceHomeomorph`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.mapped_independence_faces`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.occupiedBase`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.selectedFiber`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.selectedFiberNonempty`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.selectedGraph`
- Truth anchor: `D5/S3/Geometry/OccupiedFiberSubstitution.vertexEquiv`
- Dependency: [D5/S3/Geometry/FiniteGraphVertexSubstitution](FiniteGraphVertexSubstitution.md)
