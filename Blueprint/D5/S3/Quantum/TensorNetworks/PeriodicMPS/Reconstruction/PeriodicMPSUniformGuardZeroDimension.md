# Hausdorff dimension of the native periodic MPS guard-zero locus

## Abstract

Hausdorff dimension of the native periodic MPS guard-zero locus

**Theorem 1.1 (The spectral guard in native coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.nativeGuard_eq_physicalGuard`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.nativeGuard_eq_physicalGuard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pullback of the ambient spectral-localization guard is the physical guard as a complex multivariate polynomial in the five Cartesian slice coordinates.

**Theorem 1.2 (Dimension with nonzero mixed trace).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.dimH_nativeGuard_zero_of_mixedTrace_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.dimH_nativeGuard_zero_of_mixedTrace_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the nonzero aligned mixed-trace sector the zero locus of the native guard has real Hausdorff dimension at most six.

**Theorem 1.3 (Dimension of the full guard-zero locus).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.dimH_nativeGuard_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.dimH_nativeGuard_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full native guard-zero locus has real Hausdorff dimension at most six in the ambient space of ordinary trace-one parameters. The proof takes the union of the nonzero mixed-trace bound and the six-dimensional zero mixed-trace sector.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.dimH_nativeGuard_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.dimH_nativeGuard_zero_of_mixedTrace_ne_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension.nativeGuard_eq_physicalGuard`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralCoefficients](Geometry/PeriodicMPSUniformSpectralCoefficients.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard](PeriodicMPSUniformPhysicalAlgebraicGuard.md)
