# Equal Gram Unitary Extension

## Abstract

Equal complex column Gram matrices admit a unitary taking one rectangular matrix to the other.

**Theorem 1.1 (One unitary on the whole common codomain).**

$$\forall A,B: Matrix\left(m, n, Complex\right),\ gram\left(B\right) = gram\left(A\right) \implies\ \exists U: Unitary\left(m, Complex\right), B = U A$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq` (`✓ std3`). ∎

*Citation.* Sirui Lu and TNLean contributors (2026). *Gram equality and unitary extension for rectangular matrices*. URL: <https://github.com/LionSR/QICLean/blob/cdaa636d1f41560f7caca7077c11068229cb9727/QICLean/Algebra/MatrixGramUnitary.lean>.

*Commentary.*

Let m and n be finite types, and A and B complex m-by-n matrices. If their column Gram matrices A* A and B* B agree, with star denoting conjugate transpose, there is a unitary U on the full m-dimensional codomain such that B=UA. Gram equality identifies all linear dependencies among the columns. It defines an isometry between their ranges through the quotient by the kernel, and finite-dimensional isometry extension supplies U. Rank-deficient matrices and empty column types are included.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq`
