# The Gram-determinant Cauchy–Schwarz inequality

## Abstract

For complex m×k matrices U and V, |det(U*V)|² ≤ det(U*U) det(V*V).

**Theorem 1.1 (Gram determinants satisfy Cauchy–Schwarz).**

Lean statement: `D5/S3/Quantum/Schatten/GramDeterminantCauchySchwarz.gram_cauchy_schwarz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/GramDeterminantCauchySchwarz.gram_cauchy_schwarz` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *MathOverflow 512579, revision 1: The elementary symmetric inequality for a Hermitian Jordan product*. DOI: [10.5281/zenodo.23920583](https://doi.org/10.5281/zenodo.23920583). URL: <https://doi.org/10.5281/zenodo.23920583>.

*Commentary.*

For complex m×k matrices U and V, with U* the conjugate transpose, |det(U*V)|² ≤ det(U*U) det(V*V); the inequality is stated in the complex order, so it also says that the right side is real and nonnegative. Every m and k is allowed: for k = 0 both sides are 1, and for k > m both Gram determinants vanish. For a k-element set T of rows, listed in increasing order, put u_T = det U[T,:] and v_T = det V[T,:]. By the Cauchy–Binet formula det(U*V) = Σ conj(u_T) v_T, det(U*U) = Σ |u_T|² and det(V*V) = Σ |v_T|². The triangle inequality gives |det(U*V)| ≤ Σ |u_T||v_T|, and the Cauchy–Schwarz inequality for finite sums bounds the square of that sum by (Σ |u_T|²)(Σ |v_T|²). This is Lemma 2 of H. Ma and W. Zhang's note on MathOverflow 512579.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/GramDeterminantCauchySchwarz.gram_cauchy_schwarz`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](CompoundMatrices.md)
