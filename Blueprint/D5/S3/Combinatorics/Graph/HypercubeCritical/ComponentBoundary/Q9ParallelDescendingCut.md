# Height cuts and parallel descending edges

## Abstract

Height cuts and parallel descending edges

**Theorem 1.1 (Cubic degree balance determines the height cut size).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut.cut_card_heightSublevel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut.cut_card_heightSublevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A height sublevel keeps all ascending edges and counts only descending edges crossing its boundary. Internal incidences cancel between the two parity classes, so the cut size is three times their difference.

**Theorem 1.2 (Three minority pairs cannot lie along the sole mixed axis).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut.not_three_minority_pairs_one_axis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut.not_three_minority_pairs_one_axis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by the axis parity choices makes the three minority pairs parallel descending edges. They would form a three-edge cut, whereas balance forces a singleton side and thus a shared endpoint. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut.cut_card_heightSublevel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParallelDescendingCut.not_three_minority_pairs_one_axis`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeThreeCut](../BalancedCubeThreeCut.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence](Q9FoldedIncidence.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers](Q9PureParityLayers.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity](../SixtySixPointSupport/WeightLayerParity.md)
