# Normalized readout rank and the radial column

## Abstract

Normalized readout rank and the radial column

**Theorem 1.1 (Normalized readout rank and the radial column).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteReadoutDerivative.injective_fderiv_normalized_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteReadoutDerivative.injective_fderiv_normalized_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a differentiable scalar norm coordinate be nonzero at the point and let the raw Pauli readout also be differentiable there. The derivative of the readout divided by the norm is injective exactly when the joint derivative of the norm and raw readout, augmented by the raw value in an extra radial direction, is injective.

For seven sites in the trace-one, trace-zero chart, specializing the two polynomial blocks to conjugate actual invariants produces the real trace of the raw marginal followed by its nine Pauli readings.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteReadoutDerivative.injective_fderiv_normalized_iff`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactReadout](SevenSiteCompactReadout.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCertificate](SevenSiteCriticalCertificate.md)
