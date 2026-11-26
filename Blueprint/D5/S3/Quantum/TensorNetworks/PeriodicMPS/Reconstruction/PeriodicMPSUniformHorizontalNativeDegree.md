# Ambient degree of the literal Pauli readout

## Abstract

Ambient degree of the literal Pauli readout

**Theorem 1.1 (Degree of the native transfer moments).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientMoment_totalDegree_le_eight`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientMoment_totalDegree_le_eight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The aligned word expansion bounds the ambient moment for each of the eight powers used by the Hermite remainder.

**Theorem 1.2 (Degree of ambient partials).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientPartial_totalDegree_le_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientPartial_totalDegree_le_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation reduces the degree budget by one.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientMoment_totalDegree_le_eight`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHorizontalNativeDegree.ambientPartial_totalDegree_le_seven`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeRotation](UniformNativeRotation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/UniformNativeSliceReadout](UniformNativeSliceReadout.md)
