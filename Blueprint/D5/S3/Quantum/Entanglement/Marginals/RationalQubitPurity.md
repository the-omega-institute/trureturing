# Rational pure extensions of qubit marginals

## Abstract

An arithmetic criterion for a pure two-qubit extension with rational matrix entries.

**Theorem 1.1 (Rational pure qubit extensions).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity.rational_qubit_purity_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity.rational_qubit_purity_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the target reductions as the two Gram products of the amplitude matrix, with a transpose on the right reduction. A rational pure joint state exists exactly when both marginals are positive semidefinite, rational and trace one, their determinants agree, and the common determinant is a sum of two rational squares.

A nonzero column of the pure density supplies rational projective amplitudes. The determinant of their two-by-two array, divided by the diagonal entry of that column, has squared modulus equal to the marginal determinant.

For sufficiency, transpose the right marginal. The two Hermitian matrices are intertwined by a rational Hermitian matrix whose square is a positive scalar multiple of the identity. Shift the left matrix by a scalar of the required squared modulus and multiply by the intertwiner. Cayley–Hamilton reduces its Gram products to the two required marginals with the same rational scale. Dividing the outer product by that scale gives the normalized state with rational matrix entries.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity.rational_qubit_purity_iff`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension](FibRationalPureExtension.md)
