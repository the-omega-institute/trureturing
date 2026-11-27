# Spectral degree under Laurent coefficient extraction

## Abstract

Spectral degree under Laurent coefficient extraction

**Theorem 1.1 (Monomial clearing preserves the coefficient bound).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.shiftedLaurent_totalDegree_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.shiftedLaurent_totalDegree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The clearing factor translates Laurent indices. Each extracted spectral polynomial has degree bounded by the original degree.

**Theorem 1.2 (Degree survives axis specialization).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.spectralCoeffAfterSpecialization_totalDegree_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.spectralCoeffAfterSpecialization_totalDegree_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After fixing either unit parameter, taking a remaining Laurent coefficient can only remove spectral monomials.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.shiftedLaurent_totalDegree_le`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.spectralCoeffAfterSpecialization_totalDegree_le`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalChart](PeriodicMPSUniformHorizontalRadicalChart.md)
