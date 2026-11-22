# Adjacent Hamming cuts in the Huang action

## Abstract

Adjacent Hamming cuts in the Huang action

**Theorem 1.1 (An adjacent cut commutes with the full action).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_commutes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_commutes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each signed coordinate flip changes the Hamming rank by one. The square of the weighted Huang operator is a scalar operator. Its off-diagonal blocks between ranks two apart therefore vanish, which gives commutation with the action on a single adjacent cut.

**Theorem 1.2 (A cut yields a vector on its two ranks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_eigenvector`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_eigenvector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut sends an eigenvector to a solution of the same eigenvalue equation supported on the two ranks of the cut.

**Theorem 1.3 (The two rank energies count the induced edges).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_edge_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_edge_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an integral coherent switching at unit weights and eigenvalue three, the cut vector has squared norm three times the induced cut edge count on each rank. Coherence counts each edge with positive contribution, and the signed action is self-adjoint.

**Theorem 1.4 (An odd lower rank forces even cut size).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_odd_cut_even_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_odd_cut_even_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sum the exterior rows below the lower rank modulo two. Each vertex of that rank is counted once per occupied coordinate, so odd rank forces its integral energy to be even. The energy formula then makes the cut edge count even.

In the separated 120+138 case of Hong, Wu and Xia's Problem 2, translating the cube aligns the nine majority orientations of the 120-vertex component into one alternating class of Hamming cuts. Diagonal sign switching after translation preserves coherence and the unit-weight eigenvalue equation. If every axis has a 19+1 fold, the two classes have nine and 171 edges. The class that starts at odd ranks contradicts the even cut count. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_commutes`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_edge_energy`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_eigenvector`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9AdjacentHuang.cutAction_odd_cut_even_edges`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity](../SixtySixPointSupport/WeightLayerParity.md)
