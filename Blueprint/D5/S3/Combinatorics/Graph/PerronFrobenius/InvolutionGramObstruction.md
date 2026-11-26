# Polynomial continuation of the fixed kernel

## Abstract

Positive Gram kernels and the fixed space of an involution

**Theorem 1.1 (A coordinate sign change can obstruct a fixed kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction.not_forall_pos_fixed_kernel_of_anticommute`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction.not_forall_pos_fixed_kernel_of_anticommute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a real polynomial matrix D commute with an involution P. The matrix (I+P)D+(I−P) acts by 2D on the fixed space and by twice the identity on the anti-fixed space. If D has a nonzero fixed kernel at every positive value of the parameter, the determinant of this modified matrix is identically zero.

At parameter −1 the modified matrix again gives a nonzero fixed kernel vector. An involution J that conjugates D(−1) to D(1) and anticommutes with P sends that vector to a nonzero anti-fixed kernel vector of D(1). This contradicts the hypothesis that the kernel of D(1) is pointwise fixed.

**Theorem 1.2 (Singular Gram defects give strictly positive eigenvectors).**

Lean statement: `D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction.exists_positive_gram_kernel_of_det_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction.exists_positive_gram_kernel_of_det_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singular defect qI−A equal to KKᵀ has a nonzero kernel vector. For irreducible A, taking coordinatewise absolute values cannot increase its defect quadratic form. Since the defect is positive semidefinite, the absolute-value vector still lies in the kernel. Irreducibility propagates any zero of this nonnegative eigenvector through the graph, so all entries are positive.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction.exists_positive_gram_kernel_of_det_eq_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/InvolutionGramObstruction.not_forall_pos_fixed_kernel_of_anticommute`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition](IrrationalQuadraticBipartition.md)
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas](MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas.md)
