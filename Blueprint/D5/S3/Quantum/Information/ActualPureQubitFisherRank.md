# Fisher information and the qubit rank alternative

## Abstract

Spectral SLD information bounds measurement Fisher information and controls the rank-one branch.

**Theorem 1.1 (Measurement Fisher lower bound).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_fisher`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_fisher` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every differentiable positive curve with the exact affine measurement probabilities has spectral SLD information at least the classical Fisher information. Two-sided positivity first forces the derivative's kernel-to-kernel block to vanish (Pker D Pker = 0), producing an SLD without invertibility. Positive residual squares then give the measurement bound.

**Theorem 1.2 (Rank alternative and binary cost gap).**

Lean statement: `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_rank_alternative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_rank_alternative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual nonconstant pure-qubit readout has rank two or incurs the binary-measurement lower bound from any negative and positive score. Rank zero and rank three are excluded by the visible projection geometry.

## References

- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_fisher`
- Truth anchor: `D5/S3/Quantum/Information/ActualPureQubitFisherRank.actual_rank_alternative`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](ActualPureQubitGeometry.md)
