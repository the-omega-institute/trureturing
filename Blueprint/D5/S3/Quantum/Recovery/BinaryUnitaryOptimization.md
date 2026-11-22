# Optimal phases for two complex columns

## Abstract

Scalar phases attain the two-column complex norm bound.

**Theorem 1.1 (A scalar phase family dominates a vector family).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryUnitaryOptimization.phases_dominate`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryUnitaryOptimization.phases_dominate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type, real coefficients r and s, and complex unit phases z, take vectors v of norm at most one in any complex inner product space. The two-column length is the square root of the sum of squared norms of r times the sum of v and s times the sum of z times v. There is a scalar unit phase at each index whose two-column length is at least as large. Cauchy–Schwarz bounds the length by a normalized two-column dual. Keeping its off-diagonal Gram entry fixed, move the diagonal mass to the determinant-zero endpoint selected by the sign of r²−s². Aligning scalar phases attains the resulting bound, including when a dual pairing vanishes.

**Theorem 1.2 (A single phase family bounds every vector family).**

Lean statement: `D5/S3/Quantum/Recovery/BinaryUnitaryOptimization.optimal_phases`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/BinaryUnitaryOptimization.optimal_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite product of unit circles is compact and the scalar objective is continuous. A maximizing phase family therefore bounds the two-column length of every admissible vector family in every complex inner product space.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/BinaryUnitaryOptimization.optimal_phases`
- Truth anchor: `D5/S3/Quantum/Recovery/BinaryUnitaryOptimization.phases_dominate`
