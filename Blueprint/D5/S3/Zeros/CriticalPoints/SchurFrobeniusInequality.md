# Schur–Frobenius inequality and equality

## Abstract

The squared moduli of a complex matrix's eigenvalues sum to at most its squared Frobenius norm, with equality exactly for normal matrices.

**Theorem 1.1 (Eigenvalue energy and matrix energy).**

$$\sum_{k} \left|\mu_{k}\right|^{2}\leq \sum_{i} \sum_{j} \left|A_{ij}\right|^{2}, (\sum_{k} \left|\mu_{k}\right|^{2}=\sum_{i} \sum_{j} \left|A_{ij}\right|^{2}) \iff AA^{*}=A^{*}A$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurFrobeniusInequality.schur_frobenius` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every complex n by n matrix A, let the mu values be the roots of its characteristic polynomial, counted with multiplicity. Their squared absolute values sum to at most the sum of squared absolute values of all matrix entries. Equality holds if and only if A commutes with its conjugate transpose. The statement includes dimension zero.

Unitary triangularization preserves the characteristic polynomial and Frobenius norm. The diagonal contributes the eigenvalue sum; the remaining squares are nonnegative. Equality forces every off-diagonal entry to vanish. A normal triangular matrix is diagonal, giving the converse. This is a formal proof of the classical matrix inequality.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurFrobeniusInequality.schur_frobenius`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../../Quantum/Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Matrix/CommutatorGap](../../Quantum/Matrix/CommutatorGap.md)
