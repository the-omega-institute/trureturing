# Soundness of integer replay for a preconditioned root certificate

## Abstract

Soundness of integer replay for a preconditioned root certificate.

**Theorem 1.1 (Integer rows bound the real operator norms).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness.clm_bounds_of_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness.clm_bounds_of_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniform scaled errors for the integer residual and Jacobian enlarge the row bounds for the preconditioned step and the derivative defect. The row sums also bound the preconditioner in the operator norm induced by the coordinate sup norm.

**Theorem 1.2 (Strict integer comparisons certify a unique root).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness.existsUnique_zero_of_replay`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness.existsUnique_zero_of_replay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scaled residual and Jacobian bounds, integer row bounds and two strict comparisons imply existence and uniqueness in the closed ball of radius 2⁻³⁰. The theorem requires the derivative of the exact residual throughout the ball and the stated derivative drift estimate.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness.clm_bounds_of_rows`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness.existsUnique_zero_of_replay`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic](ChirpedReplayArithmetic.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedRootCertificate](ChirpedRootCertificate.md)
