# Gray reconstruction from eight uniform directions

## Abstract

Actual edge uniformity in eight directions reconstructs a balanced induced cubic 54-support as a Gray cube image.

**Theorem 1.1 (Eight actual uniform directions force Gray reconstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/EightUniformGrayReconstruction.eight_uniform_gray_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/EightUniformGrayReconstruction.eight_uniform_gray_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input is the actual finite vertex support C in Q9, regular of degree three in its induced cube graph, Huang-balanced, and of cardinality 54. Given a coordinate j, every other coordinate i has a bit b_i such that each occupied i-edge has x_i=b_i at its ORIGINAL globally even endpoint x. Nonemptiness is derived from cardinality 54. No connectedness, centered band, phase alignment, eigenvector, isomorphism or auxiliary count is an input.

The consumed private EightUniformHeightSpan argument forces span at most one for the eight-coordinate mismatch weight minus original odd parity. There are nine occupied j-edges. Their even endpoints all have the upper height and therefore the same eight-coordinate weight. At a globally even x, the parity of that weight is x_j XOR the parity of the chosen eight bits. Consequently every occupied j-edge has the same j-bit at its original even endpoint, proving the ninth uniform direction without complementing the chosen vector.

With all nine uniform bits, full mismatch weight minus original odd parity is constant on every occupied edge. A nonempty actual level is neighbor-closed; inherited cubic regularity, balance and the existing 54 lower bound make that level all of C. Choose r as the full mismatch weight of an actual original even endpoint. Then all full weights are r or r+1. The genuine cube translation that complements exactly the selected TRUE bits sends C into two adjacent literal Hamming layers. A neighbor bijection transports actual regularity, and HuangCubeCovariance.exists_signed_covariance transports the actual switching gauge and balance.

AdjacentLayerRigidity.adjacent_layers_gray_reconstruction supplies the Gray image after translation. Composing its cube equivalence with the inverse translation yields total equivalences g of Q9 and pi of Fin9, the exact law g(flip x i)=flip(g x)(pi i) for every x,i, and C=(GrayGridComponent.support 3).image g.

This is a repository-derived conditional reconstruction motivated by Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7 Problem 2: https://arxiv.org/html/2610.09483v1#Thmproblem2 . Arbitrary 54-support reconstruction, the 258-point obstruction and the original f2(Q9) problem remain unresolved. No literature-priority or original-problem resolution is claimed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/EightUniformGrayReconstruction.eight_uniform_gray_reconstruction`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AdjacentLayerRigidity](AdjacentLayerRigidity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/EightUniformHeightSpan](EightUniformHeightSpan.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](HuangCubeCovariance.md)
