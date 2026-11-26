# The determinant divisor in a four-site pencil sextic

## Abstract

The determinant divisor in a four-site pencil sextic

**Theorem 1.1 (A determinant expression for the sextic).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.four_mul_sextic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.four_mul_sextic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Four times the necklace sextic is the negative square of the triplet determinant plus the singlet times the adjugate singlet, corrected by the cube of the singlet times the triplet determinant.

**Theorem 1.2 (The mixed adjugate minor).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.cleared_pencil_minor`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.cleared_pencil_minor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic vector and Hankel moments express the relevant functionals as a bilinear pairing. The two-by-two minor yields a factor of the triplet determinant over the coefficient ring.

**Theorem 1.3 (The residual conic for an invertible factor).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.residual_conic_zero_of_sextic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.residual_conic_zero_of_sextic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mixed minor gives a determinant-free formula after clearing the constants from the two linear systems. When the cubic and the sextic vanish and the determinant divisor is nonzero, the residual conic vanishes.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.cleared_pencil_minor`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.four_mul_sextic`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualFormula.residual_conic_zero_of_sextic`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic](PeriodicMPSFourSiteSextic.md)
