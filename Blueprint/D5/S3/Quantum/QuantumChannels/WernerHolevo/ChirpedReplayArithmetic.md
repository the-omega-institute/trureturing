# Signed fixed-point error bounds for the replay

## Abstract

Signed fixed-point error bounds for the replay.

**Theorem 1.1 (Uniform error for computed roots of unity).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic.root_error`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic.root_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each frequency index in the cyclic order, the error after decoding is at most 45 divided by the fixed scale. The bound propagates the Taylor and signed-rounding errors through three rounded squarings.

**Theorem 1.2 (Signed rational bounds for phases and slopes).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic.cayley_error`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic.cayley_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational input with positive denominator gives fixed-point approximants to the Cayley phase and its slope. Each decoded approximation has error at most two divided by the fixed scale.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic.cayley_error`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplayArithmetic.root_error`
- Dependency: [D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction](../../../Analytic/Certified/TrigEnvelopePhaseReduction.md)
