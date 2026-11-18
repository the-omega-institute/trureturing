# Reconstruction from the actual thin coordinate half

## Abstract

A nonempty actual Huang-balanced induced cubic support in Q9 with a coordinate-zero half of size at most sixteen is a cube-symmetry image of the genuine Gray incidence support.

Q9 denotes Fin 9 to Bool, flip is BalancedCriticalSpectrum.flip, and H is the fixed Huang matrix from HypercubeSubQuorum. C is the original finite support; its graph is induced by actual cube adjacency. Balanced means IsBalanced C for that fixed signing. coordinateSlice C b filters C by x(0)=b. The symbol GraySupport(d) abbreviates GrayGridComponent.support d; its FALSE coordinates encode one selected position per row for points, and one empty row with one selected position in each other row for lines. Both equivalences in the conclusion are total: g acts on all cube vertices and p on all nine coordinates. The theorem assumes no face, coordinate labels, sign gauge, Gray normal form or connectedness of the original support.

**Theorem 1.1 (Thin half determines the entire original support).**

$$\forall C \in \operatorname{Finset}\left(\operatorname{Q}\left(9\right)\right),\; (\operatorname{Nonempty}\left(C\right)) \Rightarrow ((\operatorname{IsRegularOfDegree}\left(\operatorname{induce}\left(\operatorname{hypercube}\left(9\right), C\right), 3\right)) \Rightarrow ((\operatorname{IsBalanced}\left(C\right)) \Rightarrow (\forall b \in \operatorname{Bool}\left(\right),\; (\operatorname{card}\left(\operatorname{coordinateSlice}\left(C, b\right)\right) \le 16) \Rightarrow (\exists g \in \operatorname{Equiv}\left(\operatorname{Q}\left(9\right), \operatorname{Q}\left(9\right)\right),\; \exists p \in \operatorname{Equiv}\left(\operatorname{Fin}\left(9\right), \operatorname{Fin}\left(9\right)\right),\; (\forall x \in \operatorname{Q}\left(9\right),\; \forall i \in \operatorname{Fin}\left(9\right),\; g\left(\operatorname{flip}\left(x, i\right)\right) = \operatorname{flip}\left(g\left(x\right), p\left(i\right)\right)) \land (C = \operatorname{image}\left(\operatorname{GraySupport}\left(3\right), g\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction.thin_slice_gray_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each C, its nonemptiness, induced degree-three regularity and Huang balance, each Boolean b and the bound on that actual coordinate-zero half imply the displayed two equivalences, flip intertwining and exact finite-set image equality. ThinCoordinateSlice supplies an actual fifteen-vertex K3,3 once-subdivision; CubicalSubdivisionRigidity supplies six injective star directions and all its vertices. Taking O to be X flipped in direction d(false,0) writes the branches as O flipped once and the middles as O flipped in one direction from each triple. Every direction avoids coordinate zero: each occurs on an actual branch-middle edge within the fixed half. Thus O(0)=b.

The standard origin has its only FALSE entry at coordinate eight. The point and line definitions prove that the entire Gray half x(8)=FALSE consists of the six first-two-row branches and nine middles. Equiv.Perm.exists_extending_pair extends the two injective maps from Option(Bool times Fin 3): the six standard directions map to the six actual directions, and coordinate eight maps to zero. Coordinate permutation followed by Boolean translation maps the standard origin to O, intertwines every flip and identifies the two whole ambient coordinate halves.

GrayGridComponent.support_isSwitching and component_regular, together with BalancedCriticalSpectrum.ambient_eigenvector, give the full Gray eigenvector of eigenvalue three. HuangCubeCovariance constructs the signed pushforward w(y)=theta(g inverse(y)) zGray(g inverse(y)); theta is evaluated in the old coordinates. Both switchings on the common slice multiply along each edge to its actual Huang coefficient. Their product is constant along those edges. The explicit incidence paths from A0 through M0j to Bj, then through Mi0 to Ai, then to Mij propagate a single unit scalar c across the fifteen vertices. The zero extensions therefore satisfy zC=c w on the entire half, including all vertices outside that slice support.

The consumed private uniqueness argument uses full eigen-equations with the same eigenvalue. At a vertex in the known half, all same-half neighbor differences vanish. Reindexing the actual matrix row by coordinate flips leaves only the cut-edge coefficient times the opposite-half difference. That coefficient has square one, so the difference vanishes. This identifies both full eigenvectors. Their unit nonzero values recover exact equality of the original support and the image Gray support.

This conditional structural theorem is motivated by Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2 . The original f2(Q9)=3-or-4 question, E15, classification of arbitrary balanced components and the full 258-point obstruction remain unresolved. No novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction.thin_slice_gray_reconstruction`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity](CubicalSubdivisionRigidity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent](GrayGridComponent.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](HuangCubeCovariance.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice](ThinCoordinateSlice.md)
