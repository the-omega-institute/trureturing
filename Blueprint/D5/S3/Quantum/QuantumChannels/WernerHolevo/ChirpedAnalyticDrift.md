# A uniform derivative drift bound for chirped correlations

## Abstract

A uniform derivative drift bound for chirped correlations.

**Theorem 1.1 (Fréchet derivative of the correlation residual).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift.hasFDerivAt_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift.hasFDerivAt_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative differentiates both seed factors in each Hermitian pairing, followed by the specified real or imaginary projection.

**Theorem 1.2 (The derivative is globally 16-Lipschitz).**

Lean statement: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift.derivative_drift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift.derivative_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each phase sign is either plus or minus one. Parseval bounds the normalized Fourier transforms of the spectrum and its derivative. Combining the bounds for the two factors yields the stated constant in the operator norm induced by coordinate sup norms.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift.derivative_drift`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedAnalyticDrift.hasFDerivAt_residual`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedCirculantGram](ChirpedCirculantGram.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedReplaySoundness](ChirpedReplaySoundness.md)
