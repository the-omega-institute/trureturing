# The Hermitian qutrit Weyl representation

## Abstract

The Hermitian qutrit Weyl representation.

**Theorem 1.1 (Weyl reconstruction of complex matrices).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.reconstruct`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nine qutrit Weyl matrices form a trace-orthogonal coordinate system, giving reconstruction from the coefficient functional.

**Theorem 1.2 (Hermitian conjugacy of the coordinates).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.coordinate_star`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.coordinate_star` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian input, complex conjugation on a coordinate agrees with negation of its Weyl weight in the chosen phase convention.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.coordinate_star`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix.reconstruct`
- Dependency: [D5/S3/Quantum/Entanglement/QutritWeylBlochNormSeparableBound](../../../Entanglement/QutritWeylBlochNormSeparableBound.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificateCore](CovarianceCertificateCore.md)
