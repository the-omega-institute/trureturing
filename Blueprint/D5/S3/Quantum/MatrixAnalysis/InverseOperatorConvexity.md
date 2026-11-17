# Inverse Operator Convexity

## Abstract

Finite positive-definite complex matrices inherit the operator convexity of inversion.

**Theorem 1.1 (Weighted inverse inequality).**

Lean statement: `D5/S3/Quantum/MatrixAnalysis/InverseOperatorConvexity.posDef_weighted_inverse_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixAnalysis/InverseOperatorConvexity.posDef_weighted_inverse_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type and positive-definite complex matrices A and B, nonnegative real weights a and b with a+b=1 satisfy (aA+bB)⁻¹ ≤ aA⁻¹+bB⁻¹ in the matrix order. The proof transports Mathlib's C⋆-algebra convexity theorem from strict positivity and Ring.inverse to Matrix.PosDef and the nonsingular matrix inverse; A and B need not commute. This is the finite matrix bridge used by trace and divergence constructions.

## References

- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/InverseOperatorConvexity.posDef_weighted_inverse_le`
