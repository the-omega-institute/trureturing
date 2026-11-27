# Exact higher transfer coefficients at all lengths

## Abstract

Exact higher transfer coefficients at all lengths

**Theorem 1.1 (Checked transfer coefficients through degree four).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet.pathRaw_coeff_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet.pathRaw_coeff_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Along the polynomial hard-core chart paths, the coefficients of degrees two through four in seven raw marginal entries are polynomially weighted Fibonacci sequences at every length n ≥ 7. A Python calculation supplies the candidate weights. Lean verifies the sparse integer identities after clearing denominators at six, eight and ten consecutive lengths beginning at seven, respectively. The transfer recurrence extends the verified formulas to all later lengths.

**Theorem 1.2 (The fourth coefficient of the raw 11,11 population).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet.forbiddenCorner_coeff_four`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet.forbiddenCorner_coeff_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same identity gives the fourth raw coefficient at the forbidden 11,11 corner. The normalization and branch comparison are carried out in the subsequent jet calculation.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet.forbiddenCorner_coeff_four`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreHigherJet.pathRaw_coeff_eq`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreFirstJet](PeriodicMPSUniformHardCoreFirstJet.md)
