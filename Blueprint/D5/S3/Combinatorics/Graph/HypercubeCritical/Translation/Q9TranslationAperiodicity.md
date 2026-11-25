# XOR stabilizers in the nine-cube

## Abstract

Two aperiodic connected components in every subcubic 258-point support

**Theorem 1.1 (Two distinct actual components have trivial XOR stabilizers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity.exists_two_aperiodic_components`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity.exists_two_aperiodic_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U be a set of 258 vertices of Q9 whose induced subgraph has maximum degree three. Two actual connected components have singular signed Huang Gram defect at every positive coordinate weighting. At unit weights, the supported eigenvector identity forces each of these components to be cubic and balanced. Switching by the balance signs yields a positive eigenvector for the unsigned internal Gram matrix at every positive weighting.

An even-weight translation preserves the two parities. Its action P fixes the positive Gram kernel by Perron rigidity. Choose any bit changed by the translation and vary the weight on that axis. Flipping its sign conjugates the defect by the diagonal sign of the bit, which anticommutes with P. The polynomial fixed-kernel obstruction then excludes the translation.

An odd-weight translation exchanges the parities. Give one axis weight two and the rest weight one. The bipartite weighted adjacency then has the irrational Perron value √12 with rational square, so every weight-preserving permutation preserves both parities. Together the two arguments show that the 512 translations of each chosen component are distinct.

This rules out periodic components for the two weighted-saturated components of any 258-point witness for f₂(Q₉)=3 in Hong, Wu and Xia’s Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity.exists_two_aperiodic_components`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentSaturation](../ComponentBoundary/Q9ComponentSaturation.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedSaturation](../ComponentBoundary/Q9WeightedSaturation.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/HuangTranslationObstruction](HuangTranslationObstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction](../../PerronFrobenius/InvolutionGramObstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition](../../PerronFrobenius/IrrationalQuadraticBipartition.md)
