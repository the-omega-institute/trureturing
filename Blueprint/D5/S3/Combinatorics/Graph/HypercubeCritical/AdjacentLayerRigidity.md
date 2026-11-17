# Rigidity of adjacent occupied layers in Q9

## Abstract

An actual Huang-balanced induced cubic 54-support in Q9 confined to two adjacent occupied layers is a genuine Gray-support cube image.

Q9 is Fin 9 to Bool, occupied x is the literal TRUE-coordinate support, and the hypotheses refer to the original finite support C, its induced cube graph and the fixed Huang balance. The layer condition is imposed on the supplied support itself; no graph, congruence or coordinate labeling is assumed.

**Theorem 1.1 (Adjacent layers force Gray reconstruction).**

$$\forall C \in \operatorname{Finset}\left(\operatorname{Q}\left(9\right)\right),\; (\operatorname{Nonempty}\left(C\right)) \Rightarrow ((\operatorname{IsRegularOfDegree}\left(\operatorname{induce}\left(\operatorname{hypercube}\left(9\right), C\right), 3\right)) \Rightarrow ((\operatorname{IsBalanced}\left(C\right)) \Rightarrow ((\operatorname{card}\left(C\right) = 54) \Rightarrow (\forall r \in \operatorname{Nat}\left(\right),\; (\forall x \in \operatorname{Q}\left(9\right),\; (x \in C) \Rightarrow ((\operatorname{card}\left(\operatorname{occupied}\left(x\right)\right) = r) \lor (\operatorname{card}\left(\operatorname{occupied}\left(x\right)\right) = r + 1))) \Rightarrow (\exists g \in \operatorname{Equiv}\left(\operatorname{Q}\left(9\right), \operatorname{Q}\left(9\right)\right),\; \exists pi \in \operatorname{Equiv}\left(\operatorname{Fin}\left(9\right), \operatorname{Fin}\left(9\right)\right),\; (\forall x \in \operatorname{Q}\left(9\right),\; \forall i \in \operatorname{Fin}\left(9\right),\; g\left(\operatorname{flip}\left(x, i\right)\right) = \operatorname{flip}\left(g\left(x\right), pi\left(i\right)\right)) \land (C = \operatorname{image}\left(\operatorname{GraySupport}\left(3\right), g\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/AdjacentLayerRigidity.adjacent_layers_gray_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal occupied-face image transfers actual cube adjacency to a finite face family. Cubic bipartite handshake gives 27 faces in each of the two layers. Huang's actual exterior zero-flow parity makes every unselected (r-1)-face degree even and every unselected (r+1)-face incidence even, while selected upper faces have incidence three. The ordered distinct-pair intersection/union bijection and Finset.offDiag_card give the exact pair double count. Reduction in ZMod 8 gives 54r congruent to 324 modulo 8, hence r congruent to 2 modulo 4; the bounds 2 ≤ r ≤ 6 then give r=2 or r=6.

For r=2 the selected pairs form an actual coordinate graph. Selected triples are exactly its triangles; an unselected triple cannot have one selected pair, by the same actual exterior parity. Every edge has three common neighbors. Thus adjacent degrees sum to twelve, every nonisolated vertex lies in a triangle, and degree sums on the three triangle edges force every coordinate degree to be six. Incidence counting gives nine selected triples through each coordinate, hence the literal TRUE half has 6+9=15 vertices. For r=6 the same unsigned incidence argument is applied after taking actual complements, giving fifteen vertices in the literal FALSE half.

The existing ThinSliceGrayReconstruction theorem is then applied unchanged to that actual coordinate half. The result supplies total equivalences of Q9 and Fin9, intertwines every actual flip with the coordinate permutation, and gives exact equality with GrayGridComponent.support 3. This proves only the adjacent layer theorem; the original universal 54-support problem, E15, threshold19 and the 258-point obstruction remain outside this statement.

The external anchor is Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2: https://arxiv.org/html/2610.09483v1#Thmproblem2 . No literature priority or resolution of that original open problem is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/AdjacentLayerRigidity.adjacent_layers_gray_reconstruction`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ThinSliceGrayReconstruction](ThinSliceGrayReconstruction.md)
