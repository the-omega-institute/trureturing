# The rank-seven normalized marginal differential

## Abstract

The rank-seven normalized marginal differential

**Theorem 1.1 (Seven independent real readouts).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet.regularReadout_rank_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet.regularReadout_rank_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every length n ≥ 7 the derivative at the witness of four real and three imaginary components of the normalized adjacent-pair matrix has real rank seven. Explicit Fibonacci coefficient formulas yield invertible real and imaginary blocks once the imaginary part of the first chart coordinate is fixed.

**Theorem 1.2 (Local coordinates from the regular readouts).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet.local_regular_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet.local_regular_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adjoining the imaginary part of the first chart coordinate makes the derivative invertible. The inverse function theorem turns the augmented readout into local coordinates around the witness.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet.local_regular_reconstruction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet.regularReadout_rank_seven`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreQuarticSign](PeriodicMPSUniformHardCoreQuarticSign.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence](PeriodicMPSUniformHardCoreTransferRecurrence.md)
