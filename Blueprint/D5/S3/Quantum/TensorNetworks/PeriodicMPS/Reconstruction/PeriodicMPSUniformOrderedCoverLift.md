# The common-divisor lift to the ordered cover

## Abstract

The common-divisor lift to the ordered cover

**Theorem 1.1 (The common-divisor lift to the ordered cover).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.exists_horizontal_heightOne_of_basicGuard`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.exists_horizontal_heightOne_of_basicGuard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An irreducible native common divisor surviving the basic guard lifts to a height-one prime containing all ordered cofactors. Its contraction to native coordinates is the divisor ideal and its contraction to the homogeneous root ring is zero.

**Theorem 1.2 (The basic guard contains every common divisor under horizontal exclusion).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.native_commonDivisor_dvd_basicGuard_of_no_horizontal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.native_commonDivisor_dvd_basicGuard_of_no_horizontal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume that no height-one prime of the ordered chart has zero root-ring contraction and contains every ordered cofactor. Then every irreducible native common cofactor divisor divides the basic guard in native coordinates.

**Theorem 1.3 (Guarded critical dimension under horizontal exclusion).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.dimH_guarded_criticalCoordinates_le_of_no_horizontal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.dimH_guarded_criticalCoordinates_le_of_no_horizontal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same ordered-prime exclusion at the given suffix length, the critical set of the actual normalized observation has Hausdorff dimension at most six on the nonzero mixed-trace and basic guard open.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.dimH_guarded_criticalCoordinates_le_of_no_horizontal`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.exists_horizontal_heightOne_of_basicGuard`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift.native_commonDivisor_dvd_basicGuard_of_no_horizontal`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbient](Geometry/PeriodicMPSUniformVerticalAmbient.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverNative](PeriodicMPSUniformOrderedCoverNative.md)
