# Motzkin Path Transfer Determinants

## Abstract

Motzkin path convolution expresses a shifted Hankel determinant as a path transfer determinant.

**Theorem 1.1 (Triangularity of the Motzkin array).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.motzkin_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.motzkin_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every nonnegative path length n, M_{n,k}(t,s) vanishes whenever k is greater than n, and M_{n,n}(t,s) = 1. Reaching height n in n steps requires every step to be an up step.

**Theorem 1.2 (The Hankel transfer identity).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.hankelDet_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.hankelDet_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For all nonnegative integers m and n, d_m(n,t,s) equals the determinant of the n by n matrix with entry M_{m+i,j}(t,s) in row i and column j, with indices starting at zero. Convolution factors the Hankel matrix as this transfer matrix times the transpose of the lower triangular Motzkin array. That triangular array has diagonal entries one and determinant one.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.hankelDet_transfer`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer.motzkin_triangle`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs](CiglerMotzkinHankelDefs.md)
