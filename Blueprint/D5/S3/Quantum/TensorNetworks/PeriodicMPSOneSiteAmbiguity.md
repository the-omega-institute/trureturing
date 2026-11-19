# Generic one-site ambiguity for periodic binary bond-two states

## Abstract

Generic one-site ambiguity for periodic binary bond-two states

**Theorem 1.1 (Collective rotations inside a one-site fiber).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.arbitrarily_close_one_site_collisions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.arbitrarily_close_one_site_collisions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotate every physical leg by the exponential of the same one-site density times an imaginary parameter. The one-site density commutes with the rotation. The derivative of the adjacent pair density is the commutator with the sum of the two local generators, multiplied by the imaginary unit.

**Theorem 1.2 (Density of the commutator witness).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.actual_locus_open_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.actual_locus_open_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutator is continuous in the amplitudes and real analytic in the tensor entries. A common parity presentation gives a nonzero commutator entry at every ring length at least four. The real analytic identity theorem gives density on the parameter space, which maps continuously onto the actual state image.

**Theorem 1.3 (Nearby unit-phase classes in the same fiber).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.generic_one_site_ambiguity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.generic_one_site_ambiguity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each state on the relatively open dense locus has arbitrarily close actual competitors with identical one-site density and different adjacent pair density. A unit phase would preserve the adjacent pair density.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.actual_locus_open_dense`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.arbitrarily_close_one_site_collisions`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSOneSiteAmbiguity.generic_one_site_ambiguity`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity](PeriodicMPSAmbiguityDensity.md)
