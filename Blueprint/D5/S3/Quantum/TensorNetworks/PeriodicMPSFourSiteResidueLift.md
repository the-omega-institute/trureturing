# An exact coefficient certificate at a physical four-site tensor

## Abstract

An exact coefficient certificate at a physical four-site tensor

**Theorem 1.1 (The selected 44 by 44 coefficient minor).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift.quotient_finrank_le_of_residualMinor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift.quotient_finrank_le_of_residualMinor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Selected monomial multiples of the cubic, conic and quartic lie in the degree-eight kernel. Their coefficient minor gives the quotient dimension bound in every field where it is nonzero.

**Theorem 1.2 (A Gaussian-integer witness).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift.physical_certificate_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift.physical_certificate_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two mod-five tensor pairs come from one Gaussian-integer tensor and its conjugate. The Lean kernel checks a right inverse of the specialized minor and the remaining nonzero factors. The nonzero product transfers to the complex tensor through the Gaussian-integer embedding.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift.physical_certificate_nonzero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidueLift.quotient_finrank_le_of_residualMinor`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample](PeriodicMPSFourSiteResidualSample.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem](PeriodicMPSFourSiteResidualSystem.md)
