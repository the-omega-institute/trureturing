# Weighted outward Huang differentials

## Abstract

Weighted outward Huang differentials

**Theorem 1.1 (Center distance determines difference energy).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.outward_sub_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.outward_sub_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The centered outward differential retains the signed coordinate flips that increase distance from the center. Changing the center reverses the direction masks exactly on separating coordinates. Reindexing by a double flip cancels the mixed energy terms because of Huang square curvature. The resulting energy is the input energy times the sum of squared weights on the separating coordinates.

**Theorem 1.2 (The outward differential squares to zero).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.outward_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.outward_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each restricted coordinate flip has square zero. Two different restricted flips anticommute. Their weighted sum therefore has square zero.

**Theorem 1.3 (Energy balance under three-center cancellation).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.closed_triple_energy_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.closed_triple_energy_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the first center's differential to three residuals that sum to zero and are each closed under their own differential. The two remaining images are opposite. The difference energy identity equates their energies with the two distances from the first center, measured by the squared coordinate weights.

For unit weights the distances are Hamming distances. Cycling the argument relates all three energies to the opposite center distances. This provides an algebraic constraint for the paired-fibre approach to Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.closed_triple_energy_relation`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.outward_sq`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference.outward_sub_energy`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
