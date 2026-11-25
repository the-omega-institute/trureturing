# Rational rank at a prescribed Fibonacci coupling

## Abstract

Exact rational rank-two completion at a prescribed Fibonacci coupling.

**Theorem 1.1 (Rational rank at most two at a prescribed coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentRank.rational_rank_le_two_at_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentRank.rational_rank_le_two_at_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive middle occupation, normalized rational edge data and a rational unobserved coupling. A rational positive semidefinite trace-one extension of rank at most two exists exactly when both Schur residual marginals are positive semidefinite, their determinants agree and the common determinant is a sum of two rational squares.

The invertible Schur elimination preserves rank and leaves a one-dimensional pivot beside the joint endpoint residual. Elimination and restoration both preserve rational entries. When the common residual trace is positive, dividing by that trace reduces rank one of the joint residual to the rational two-qubit purity criterion. The determinants scale by a rational square, so the arithmetic test can use the unnormalized residuals. At trace zero both residuals vanish and restoring the pivot gives rank one.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentRank.rational_rank_le_two_at_iff`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension](FibCoherentExtension.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity](RationalQubitPurity.md)
