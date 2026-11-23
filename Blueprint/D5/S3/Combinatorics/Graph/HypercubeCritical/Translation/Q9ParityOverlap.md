# Parity intersections of translated cubic supports

## Abstract

Balanced cubic nine-cube supports have no one-vertex parity intersection under XOR translation.

**Theorem 1.1 (A translated intersection on either parity has cardinality different from one).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9ParityOverlap.parity_overlap_card_ne_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9ParityOverlap.parity_overlap_card_ne_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C and D be supports in the Boolean nine-cube. Assume each induced graph is 3-regular and switching-balanced for Huang's fixed edge signs. For every XOR translation a and each parity b, the number of vertices of parity b in the intersection of C with a + D differs from one. The zero translation gives the same test for C and D.

XOR preserves induced adjacency and degree. Huang edge covariance supplies a diagonal sign that transports the switching function. The ambient eigenvector theorem gives an eigenvalue-3 switching vector with entries 0 and ±1. Reducing those entries modulo 3 and retaining a single parity gives a Huang kernel word with exactly the selected support on that parity.

The symmetric unit-weight Huang matrix over the ternary field has image equal to kernel because the sum of the nine squared weights vanishes and a coordinate weight is nonzero. Any two kernel words therefore pair to zero. A singleton intersection contributes one nonzero product to that pairing, a contradiction.

In the nine-cube component geometry of Hong–Wu–Xia Problem 2, this excludes any relative placement of balanced cubic components that creates exactly one shared vertex on a parity. The test also applies to self-translates and disconnected balanced cubic supports. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9ParityOverlap.parity_overlap_card_ne_one`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](../BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](../ComponentBoundary/Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells](../ComponentBoundary/Q9SignedContactCells.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram](../ComponentBoundary/Q9WeightedBoundaryGram.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/HuangTranslationObstruction](HuangTranslationObstruction.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeSubQuorum](../../HypercubeSubQuorum.md)
