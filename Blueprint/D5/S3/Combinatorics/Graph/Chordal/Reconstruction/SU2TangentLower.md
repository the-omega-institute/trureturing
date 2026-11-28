# Tangent transfer and round quaternion obstructions

## Abstract

Round unit-quaternion reconstruction dominates three-dimensional Euclidean reconstruction on each fixed finite connected graph.

**Theorem 1.1 (Fixed-graph tangent transfer).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.fixed_graph_euclidean_three_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.fixed_graph_euclidean_three_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every round unit-quaternion coefficient on a fixed finite connected graph is an admissible coefficient for three-dimensional Euclidean gains on that graph.

First-order imaginary quaternion curves encode the gains. Normalize each fitted quaternion potential at one vertex and use bounded displacements along fixed finite walks. Project the rescaled ambient differences to imaginary coordinates and remove slack by closed-range minimization.

**Theorem 1.2 (Tangent transfer at all defect scales).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.fixed_graph_euclidean_three_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.fixed_graph_euclidean_three_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The resulting Euclidean fit has error bounded by the coefficient times any nonnegative triangle-defect budget.

Scale at positive budgets and use finite-dimensional closure as the scale decreases to a zero budget.

**Theorem 1.3 (Width-four family lower bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.round_width_four_family_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.round_width_four_family_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A round coefficient that works on every finite width-four power path is at least the square root of three halves.

Apply the fixed-graph transfer and the affine regular tetrahedron obstruction to the entire family of path lengths.

**Theorem 1.4 (Finite round obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.exists_round_width_four_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.exists_round_width_four_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative coefficient strictly below the square root of three halves fails on some finite width-four power path with positive defect budget.

The family lower bound supplies gains and a budget for which each potential in the full unit-quaternion group has an edge residual exceeding the proposed bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.exists_round_width_four_obstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.fixed_graph_euclidean_three_scaled`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.fixed_graph_euclidean_three_transfer`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/SU2TangentLower.round_width_four_family_lower`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata](ChordalBanachExactStrata.md)
