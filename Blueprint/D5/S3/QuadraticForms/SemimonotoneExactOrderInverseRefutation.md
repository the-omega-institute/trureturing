# Exact semimonotone order does not imply invertibility

## Abstract

A four-dimensional singular matrix has exact semimonotone order three, so exact semimonotone order does not force a negative determinant or an inverse.

Source: Bharat Pratap Chauhan and Dipti Dubey, On semimonotone matrices of exact order two, arXiv:2603.00639v1, Section 2, Definition 3.1 and Remark 4.1, second unlettered bullet. The binding version is available at https://arxiv.org/html/2603.00639v1. The question reads: “Is it true that if A belongs to E_{0_k}, then det A < 0 and A inverse exists and is a Z-matrix?” Its introductory range is n at least three and one at most k less than n. The first bullet concerning negative-entry counts is a separate question.

**Definition 1.1 (Semimonotone).**

$$(\operatorname{Semimonotone}\left(A\right)) \Leftrightarrow (\forall (x: \iota \to \mathbb{R}), ((x \ne 0) \Rightarrow ((\forall (i: \iota), (0 \le \operatorname{x}\left(i\right))) \Rightarrow (\exists (i: \iota), ((0 < \operatorname{x}\left(i\right)) \land (0 \le \operatorname{mulVec}\left(A, x\right)_{i}))))))$$

*Formalization.* `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.Semimonotone` (`✓ std3`).

*Citation.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

For an arbitrary finite index type iota and a real square matrix A, every nonzero entrywise nonnegative real vector must have a strictly positive coordinate whose image coordinate is nonnegative. Zero coordinates are allowed. This is the ordinary E_0 predicate from Section 2, rather than strict semimonotonicity or the source's almost-class condition.

**Definition 1.2 (IsExactOrder).**

$$(\operatorname{IsExactOrder}\left(n, k, A\right)) \Leftrightarrow ((k \le n) \land ((\forall (\alpha: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((\operatorname{card}\left(\alpha\right) = n - k) \Rightarrow (\operatorname{Semimonotone}\left(A_{\alpha\alpha}\right)))) \land (\forall (\alpha: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)), ((n - k < \operatorname{card}\left(\alpha\right)) \Rightarrow (\neg \operatorname{Semimonotone}\left(A_{\alpha\alpha}\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.IsExactOrder` (`✓ std3`).

*Citation.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

Here alpha ranges over every finite subset of Fin n, card denotes its cardinality, and A with subscripts alpha alpha is the actual principal submatrix, indexed by the subtype alpha. Every block of size n-k is semimonotone, and every block of every larger size fails semimonotonicity. Sizes are automatically at most n. The condition k at most n is explicit. Fin n relabels the source's indices one through n by zero through n-1.

**Definition 1.3 (IsZMatrix).**

$$(\operatorname{IsZMatrix}\left(A\right)) \Leftrightarrow (\forall (i: \iota), (\forall (j: \iota), ((i \ne j) \Rightarrow (A_{ij} \le 0))))$$

*Formalization.* `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.IsZMatrix` (`✓ std3`).

*Citation.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

For every pair of distinct indices the corresponding entry is nonpositive, exactly the Z-matrix definition in Section 2. Diagonal entries are unrestricted.

**Definition 1.4 (claim).**

$$(claim) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((3 \le n) \Rightarrow ((1 \le k) \Rightarrow ((k < n) \Rightarrow ((\operatorname{IsExactOrder}\left(n, k, A\right)) \Rightarrow ((\operatorname{det}\left(A\right) < 0) \land ((\operatorname{IsUnit}\left(A\right)) \land (\operatorname{IsZMatrix}\left(A^{-1}\right)))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.claim` (`✓ std3`).

*Citation.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

The assertion quantifies over every natural n and k and every real n by n matrix. Its hypotheses are n at least three, one at most k, k less than n and membership in E_{0_k}. Its conclusion contains all three source requirements: negative determinant, actual invertibility, and a Z-matrix inverse. IsUnit A means that A is a unit in the matrix ring, equivalently it has a two-sided matrix inverse. Although Mathlib's inverse operation is total, IsUnit A is a separate conjunct, so the assertion does not interpret a singular matrix's total inverse as an existing inverse. There is no symmetry, Z-matrix or nonsingularity hypothesis on A.

**Definition 1.5 (counterexample).**

$$counterexample = \operatorname{ofRows}\left(\operatorname{row}\left(1, -5, -2, -2\right), \operatorname{row}\left(-5, 1, -2, -2\right), \operatorname{row}\left(-2, -2, 1, -5\right), \operatorname{row}\left(-2, -2, -5, 1\right)\right)$$

*Formalization.* `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.counterexample` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

The displayed four rows specify the real matrix A. Its diagonal is one; each off-diagonal entry is at most minus two. Each singleton principal block is [1] and is semimonotone. In every larger principal block and every row choose one other index: the diagonal and that off-diagonal entry sum to at most minus one, and all remaining entries are nonpositive. Thus the all-ones vector is nonzero and nonnegative, and every image coordinate is strictly negative. Every such block fails semimonotonicity. Consequently A belongs to E_{0_3}, with n=4 and k=3.

**Definition 1.6 (kernelVector).**

$$kernelVector = \operatorname{vector}\left(1, 1, -1, -1\right)$$

*Formalization.* `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.kernelVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

The real column vector (1,1,-1,-1) is nonzero and its product with A is zero. The equal-sized sign blocks cancel exactly: each row gives either 1-5+2+2 or -2-2-1+5. This proves singularity by ordinary matrix algebra, independently of testing finitely many numerical matrices.

**Theorem 1.7 (The full second-bullet assertion is false).**

$$\neg (\forall (n: \mathbb{N}), (\forall (k: \mathbb{N}), (\forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((3 \le n) \Rightarrow ((1 \le k) \Rightarrow ((k < n) \Rightarrow ((\operatorname{IsExactOrder}\left(n, k, A\right)) \Rightarrow ((\operatorname{det}\left(A\right) < 0) \land ((\operatorname{IsUnit}\left(A\right)) \land (\operatorname{IsZMatrix}\left(A^{-1}\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bharat Pratap Chauhan; Dipti Dubey (2026). *On semimonotone matrices of exact order two*. URL: <https://arxiv.org/abs/2603.00639>.

*Commentary.*

Specialize the universal assertion to n=4, k=3 and the displayed matrix. Exact-order membership was established for every principal index subset. A negative determinant would be nonzero, and Mathlib's kernel theorem would then force the displayed nonzero kernel vector to vanish, a contradiction. The same kernel vector also rules out an actual inverse; no property of the total inverse on singular matrices is used. The failure occurs in the allowed n-k=1 boundary case, through cancellation between two groups of coordinates with opposite signs. This refutes the universal conjunction, without asserting that every individual inverse-Z conclusion fails or settling the distinct exact-order-two conjecture.

## References

- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.IsExactOrder`
- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.IsZMatrix`
- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.Semimonotone`
- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.counterexample`
- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.kernelVector`
- Truth anchor: `D5/S3/QuadraticForms/SemimonotoneExactOrderInverseRefutation.result`
