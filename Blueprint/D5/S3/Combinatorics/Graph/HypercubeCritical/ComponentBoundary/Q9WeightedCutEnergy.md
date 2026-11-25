# Directional energy of a balanced cube support

## Abstract

Directional energy of a balanced cube support

In the nine-cube, coordinate flips generate the translation group. Their Huang-signed lifts square to the identity and anticommute in distinct directions. The central sign in this action forces the square of the weighted sum of the lifts to be the sum of the squared weights times the identity. On a balanced support, changing signs at the vertices transfers the signed edge correlations to ordinary edge correlations. This yields a joint constraint on cut sizes for Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2

**Theorem 1.1 (Balanced supports bound the joint edge correlations).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.sum_sq_direction_correlation_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.sum_sq_direction_correlation_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real vector supported on the balanced set, choose each weight to be the corresponding directional correlation after switching. Cauchy–Schwarz then bounds the sum of the squared correlations by the squared total mass.

**Theorem 1.2 (Cut shores jointly constrain their edge directions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_direction_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_direction_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a test vector taking constant values on the two shores. Each correlation splits into the two internal endpoint counts and twice the crossing count. Varying the constants tests all directions simultaneously.

**Theorem 1.3 (Uniform direction counts force a nonpositive cut discriminant).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_count_discriminant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_count_discriminant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cubic degree sum and uniform direction counts cancel the terms of highest degree. The remaining real quadratic must be nonnegative for every value of the sum of the two test constants when their difference is one.

**Theorem 1.4 (Missing directions bound the shore order of a nine-edge cut).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_shore_capacity_of_nine_crossings`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_shore_capacity_of_nine_crossings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a 90-vertex balanced cubic count profile, suppose exactly three directions cross the cut, with three crossing edges in each. Completing the square after separating the crossing and noncrossing directions bounds an odd shore at 31 vertices if it lacks a noncrossing internal direction and at 39 if it lacks a crossing internal direction. The estimate uses the signed coordinate action and the two-shore counts.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_count_discriminant`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_direction_energy`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.cut_shore_capacity_of_nine_crossings`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedCutEnergy.sum_sq_direction_correlation_le`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells](Q9SignedContactCells.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedBoundaryGram](Q9WeightedBoundaryGram.md)
