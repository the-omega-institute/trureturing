# The exact covariance certificate

## Abstract

The exact covariance certificate.

**Theorem 1.1 (Shifted Gram factorization).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.ldl_entries`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.ldl_entries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every block has the displayed LDL factorization after subtracting one fifth of the identity. The arithmetic is exact in the rational quadratic coefficient ring.

**Theorem 1.2 (Equality of quartic coefficients).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.coefficient_equality`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.coefficient_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checker compares every entry of the target covariance matrix with the sum of the Weyl-weight Gram forms.

**Theorem 1.3 (Positive semidefiniteness on Hermitian coefficients).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted factorizations and positive pivots yield nonnegative Gram forms. The coefficient equality identifies their sum with the covariance matrix for every conjugation-compatible Weyl coefficient vector.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.coefficient_equality`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_posSemidef`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.ldl_entries`
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataA](CovarianceCertificateDataA.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataB](CovarianceCertificateDataB.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateDataC](CovarianceCertificateDataC.md)
