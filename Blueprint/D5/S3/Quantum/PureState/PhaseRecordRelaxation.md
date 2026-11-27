# Effects attaining a feasible diagonal profile

## Abstract

Orthogonality makes the diagonal budget sharp in the effect relaxation.

**Theorem 1.1 (Every feasible profile attains its relaxed score for flat orthogonal phases).**

Lean statement: `D5/S3/Quantum/PureState/PhaseRecordRelaxation.relaxed_effects_attain`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PhaseRecordRelaxation.relaxed_effects_attain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sandwich each normalized phase effect by the diagonal matrix with entries √dᵢ. Column orthogonality gives sum diag(d), hence a positive family with total effect bounded by the identity and total trace at most M. For each of the N labels, the phases cancel in the rank-one pairing and the score is the square of the profile value divided by N. Common-channel realizability is addressed separately by the finite Fourier construction.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PhaseRecordRelaxation.relaxed_effects_attain`
- Dependency: [D5/S3/Quantum/PureState/QuantumMemoryBudget](QuantumMemoryBudget.md)
