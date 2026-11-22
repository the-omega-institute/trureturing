# Continuity at fixed reference

## Abstract

For a fixed second matrix, geodesic relative entropy is continuous in the first matrix on the positive semidefinite cone.

**Theorem 1.1 (Positivity of the modular matrix).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.geodesicModular_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.geodesicModular_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

A positive semidefinite first matrix gives positive semidefinite powers. The inverse square root of the second matrix is self-adjoint in the real continuous functional calculus, and congruence preserves positivity of the right factor.

**Theorem 1.2 (Continuity of the modular matrix).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.continuousOn_geodesicModular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.continuousOn_geodesicModular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

For 0 ≤ t ≤ 1, the two matrix powers vary continuously on the positive semidefinite cone. At t = 1 the left power is the identity, including at singular first matrices. The second matrix is fixed.

**Theorem 1.3 (Continuity of the spectral quadratic form).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.continuousOn_geodesicRelativeEntropy`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.continuousOn_geodesicRelativeEntropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Continuity of z log z at zero gives continuity after applying the spectral function to the modular matrix. Pairing with the fixed reference vector proves first-argument continuity for each 0 ≤ t ≤ 1. The forward construction uses this theorem with a faithful reference held fixed during each regularization.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.continuousOn_geodesicModular`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.continuousOn_geodesicRelativeEntropy`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity.geodesicModular_posSemidef`
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular](CapelCostaRicoGeodesicModular.md)
