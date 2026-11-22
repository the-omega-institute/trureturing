# Exceptional slices of the physical transfer guard

## Abstract

Exceptional slices of the physical transfer guard

**Theorem 1.1 (The two exceptional slices).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.eval_physicalGuard_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.eval_physicalGuard_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the real aligned slice with k > 0, the physical transfer guard vanishes precisely when d = 0 or d = −conj(e). Here d = x₀ + i x₃ and e = x₂ + i x₄.

**Theorem 1.2 (Dimension in the nonzero mixed-trace sector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.dimH_physicalGuard_zero_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.dimH_physicalGuard_zero_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The guard-zero locus with nonzero aligned mixed trace has real Hausdorff dimension at most six in ordinary trace-one parameters. Each slice uses three real coordinates. The physical charts add three real rotation coordinates and use two stereographic phase frames.

**Theorem 1.3 (Dimension of zero aligned mixed trace).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.dimH_zeroMixed_parameters_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.dimH_zeroMixed_parameters_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero aligned mixed-trace sector has real Hausdorff dimension at most six in ordinary trace-one parameters. Its differentiable parametrization uses three complex coordinates.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.dimH_physicalGuard_zero_le`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.dimH_zeroMixed_parameters_le`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformPhysicalAlgebraicGuard.eval_physicalGuard_eq_zero_iff`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformCompactGraph](PeriodicMPSUniformCompactGraph.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphCriticalDimension](SevenSiteGraphCriticalDimension.md)
