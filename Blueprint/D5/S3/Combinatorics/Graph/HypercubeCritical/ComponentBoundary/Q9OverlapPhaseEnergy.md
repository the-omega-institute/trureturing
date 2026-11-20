# Energy of a signed overlap

## Abstract

Signed energy bounds overlap between balanced cubic supports

**Theorem 1.1 (The seven retained directions bound the internal degree of a phase).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy.phase_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy.phase_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the intersection of two Huang-balanced cubic supports, the ratio of the two switching functions is either +1 or −1. Each ratio defines a phase L. A common internal edge preserves the ratio, so edges leaving a phase within either parent end outside their intersection.

When the internal edges at L avoid two axes, apply the sum of the seven remaining signed flips to the switching function supported on L. Its squared norm is 7|L| by anticommutation. The values on L contribute the squared internal degrees. The two parent exit regions are disjoint and contribute at least their edge incidence counts. If p is the internal degree sum and n₀ and n₁ count degrees zero and one, this gives 3p+6n₀+2n₁≤7|L|.

**Theorem 1.2 (Two-axis translation puts the estimate on separated components).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy.translated_phase_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy.translated_phase_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate one of two separated supports by flipping two coordinates. A vertex in the resulting intersection represents a pair at Hamming distance two. An internal edge along either flipped coordinate would give an edge between the original supports. The remaining internal degree therefore counts the directions shared by both vertices of the pair. This applies to the 258-vertex question of Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2).

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy.phase_energy_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OverlapPhaseEnergy.translated_phase_energy_bound`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord](../TwentyPointEightWord.md)
