# Affine restriction and first derivatives of the seven-site observation

## Abstract

Affine restriction and first derivatives of the seven-site observation

**Theorem 1.1 (Degree of the affine restriction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation.natDegree_affineRestriction_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation.natDegree_affineRestriction_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any polynomial in the five slice coordinates over a commutative ring, substitution of the specified affine line gives a univariate polynomial whose natural degree is at most the original total degree.

**Theorem 1.2 (First partial at a slice point).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation.eval_partial`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation.eval_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any slice point and Pauli observation entry over a commutative ring, evaluation of the formal partial equals the corresponding square-zero coefficient of the observation. The coordinate direction supplies the square-zero input.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation.eval_partial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteLineEvaluation.natDegree_affineRestriction_le`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCertificate](SevenSiteCriticalCertificate.md)
