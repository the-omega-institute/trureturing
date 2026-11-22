# Identification of analytic residuals and Jacobians with replay rows

## Abstract

Identification of analytic residuals and Jacobians with replay rows.

**Theorem 1.1 (The analytic residual equals the exact replay residual).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge.residual_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge.residual_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For valid left and right seed layouts in each row, the modular permutation and the replay index have the same action when the unit represents the supplied inverse. The residual sums agree under the common real or imaginary projection.

**Theorem 1.2 (The analytic derivative matrix equals the exact replay Jacobian).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge.jacobian_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge.jacobian_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same layout and inverse hypotheses, evaluation on a coordinate basis vector identifies each derivative entry with the sum of the two seed slope terms in the replay.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge.jacobian_eq`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticReplayBridge.residual_eq`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift](ChirpedAnalyticDrift.md)
