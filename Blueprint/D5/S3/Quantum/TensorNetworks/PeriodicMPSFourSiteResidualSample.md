# Residual equations at a four-site specialization

## Abstract

A degree-eight residual quotient certificate in characteristic five

**Theorem 1.1 (The specialization comes from actual tensors).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.sample_necklace_values`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.sample_necklace_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the six necklace traces of two explicit pairs of binary bond-two tensors gives the source triplet matrices over the field with five elements.

**Theorem 1.2 (Coefficient identities for the two pencils).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.sample_pencil_decompositions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.sample_pencil_decompositions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any commutative ring of characteristic five, the two sextics decompose into a cubic product equation times a cubic and a determinant divisor times a conic. Adjugate substitution on the second conic gives a quartic in the first pencil.

**Theorem 1.3 (A one-dimensional bound at degree eight).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.residual_sample_degree_eight_rank`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.residual_sample_degree_eight_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the homogeneous quotient by the cubic, conic and quartic, reductions send every degree-eight monomial into the span of the eighth power of the first coordinate. This bounds the degree-eight quotient image over every field of characteristic five.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.residual_sample_degree_eight_rank`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.sample_necklace_values`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteResidualSample.sample_pencil_decompositions`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic](PeriodicMPSFourSiteSextic.md)
