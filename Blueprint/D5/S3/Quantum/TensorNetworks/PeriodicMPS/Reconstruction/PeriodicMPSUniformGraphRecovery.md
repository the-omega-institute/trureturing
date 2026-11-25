# Uniform two-site recovery from a critical-locus dimension bound

## Abstract

Uniform two-site recovery from a critical-locus dimension bound

**Theorem 1.1 (Uniform two-site recovery from a critical-locus dimension bound).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphRecovery.generic_twoSite_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphRecovery.generic_twoSite_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix m with n = 2 + m ≥ 7. If the ordinary trace-one chart's critical coordinate set for the normalized adjacent-pair observation has real Hausdorff dimension at most six, there is a relatively Euclidean-open dense subset of the compact closure of the actual periodic binary bond-two projector image. Each target in that subset is an actual projector. Every competitor in the compact closure with the same normalized adjacent-pair marginal equals the target projector. Thus actual unit-mass competitors agree up to unit phase. Relative openness and density use the real Euclidean topology. The proof combines the compact graph boundary bound, the hard-core singleton neighborhood, and compact regular-fiber continuation.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphRecovery.generic_twoSite_recovery`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/CompactRegularFiberContinuation](CompactRegularFiberContinuation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphBoundary](PeriodicMPSUniformGraphBoundary.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreCompactRecovery](PeriodicMPSUniformHardCoreCompactRecovery.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformLinearTraceLift](PeriodicMPSUniformLinearTraceLift.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactReadout](SevenSiteCompactReadout.md)
