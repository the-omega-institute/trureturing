# The covariance inequality for actual qutrit observables

## Abstract

The covariance inequality for actual qutrit observables.

**Theorem 1.1 (Compression to two physical observables).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.physical_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.physical_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A diagonal and a circulant Hermitian observable expand in the two Weyl subspaces. Their covariance matrix is a compression of the polynomial Gram matrix.

**Theorem 1.2 (The bound at the actual qutrit square root).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.bob_raw_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.bob_raw_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant inequality of the two-by-two positive covariance matrix gives the squared real cross term plus nine quarters of the squared imaginary cross term. Taking the actual square root provides the raw bound for every positive semidefinite trace-one qutrit state.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.bob_raw_covariance`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.physical_posSemidef`
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate](CovarianceCertificate.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix](CovarianceWeylMatrix.md)
