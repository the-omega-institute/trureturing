# Generic recovery of the four-site periodic binary bond-two state

## Abstract

Generic recovery of the four-site periodic binary bond-two state

**Theorem 1.1 (Recovery on a relatively open dense part of the actual state image).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity.generic_unitPhase_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity.generic_unitPhase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm square of the coefficient certificate is a real polynomial in the full amplitudes. Its pullback to the real tensor coordinates is nonzero at a physical witness. Polynomial density and the continuous parametrization give the relatively open dense locus, with unit-phase uniqueness against every actual competitor.

**Theorem 1.2 (Recovery in the unit-mass slice).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity.normalized_generic_unitPhase_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity.normalized_generic_unitPhase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive rays of the certificate locus meet the unit-mass slice in a relatively open dense set. Rescaling both tensor pairs preserves equality of the two-site marginal and transports unit-phase recovery to this slice.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity.generic_unitPhase_recovery`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteGenericity.normalized_generic_unitPhase_recovery`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity](OpenBoundaryMPSDensityGenericity.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteRecovery](PeriodicMPSFourSiteRecovery.md)
