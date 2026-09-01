# Hermitian Kernel Negative Squares

## Abstract

Finite Gram inertia defines the negative squares of a Hermitian kernel.

**Definition 1.1 (Hermitian kernel).**

Lean statement: `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.HermitianKernel`

*Formalization.* `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.HermitianKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A complex kernel is Hermitian when exchanging its two points and taking complex conjugation recovers the original value.

**Definition 1.2 (Exactly kappa negative squares).**

Lean statement: `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.HasNegativeSquares`

*Formalization.* `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.HasNegativeSquares` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite sampling family produces a Hermitian Gram matrix. The kernel has exactly kappa negative squares when every such matrix has at most kappa negative eigenvalues and at least one finite family attains exactly kappa.

Both the uniform upper bound and its finite attainment are part of the definition; neither clause is inferred from the other.

**Theorem 1.3 (A kernel with one negative square exists).**

$$\exists K: \operatorname{HermitianKernel}\left(Unit\right), \operatorname{HasNegativeSquares}\left(K, 1\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.exists_hermitian_kernel_with_one_negative_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant minus-one kernel on Unit is a nontrivial realization. Every finite Gram matrix has negative index at most one by the rank-one positive-update bound.

Sampling the unique point once gives the one-by-one matrix with entry minus one, whose sole eigenvalue is negative, so the upper bound is attained.

## References

- Truth anchor: `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.HasNegativeSquares`
- Truth anchor: `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.HermitianKernel`
- Truth anchor: `D5/S3/Weil/Pick/HermitianKernelNegativeSquares.exists_hermitian_kernel_with_one_negative_square`
- Dependency: [D5/S3/Weil/ZetaLinear/PoleCapacityRankOne](../ZetaLinear/PoleCapacityRankOne.md)
