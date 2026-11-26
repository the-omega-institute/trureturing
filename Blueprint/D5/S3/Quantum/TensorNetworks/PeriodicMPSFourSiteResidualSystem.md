# Eliminating the projective partner in the four-site marginal

## Abstract

Eliminating the projective partner in the four-site marginal

**Theorem 1.1 (The degrees of the three eliminated equations).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem.residualEquations_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem.residualEquations_degree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left product constraint has degree three, the left conic has degree two, and the right conic pulled back by the adjugate has degree four.

**Theorem 1.2 (Compatible invertible triplets are proportional under the rank bound).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem.triplets_proportional`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem.triplets_proportional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both factors satisfy the triplet sextic. The shared forward and reverse products put every competitor in the same power pencil. The adjugate partner and the singlet product supply three residual equations. The degree-eight quotient bound then identifies the projective left factor.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem.residualEquations_degree`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSystem.triplets_proportional`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula](PeriodicMPSFourSiteResidualFormula.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualRank](PeriodicMPSFourSiteResidualRank.md)
