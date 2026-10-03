# Orthogonal Moments for Motzkin Columns

## Abstract

One orthogonal moment functional recovers every column of the boundary-weighted Motzkin triangle.

**Theorem 1.1 (The column moment functional).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer.column_moments`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer.column_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Over the integer polynomial ring in t and s, let p_0(y) = 1, p_1(y) = y - s and p_{r+2}(y) = (y - t)p_{r+1}(y) - p_r(y). There is a linear functional ell on polynomials in y such that ell(y^n p_k(y)) = M_{n,k}(t,s) for all nonnegative n and k, and ell(p_i p_j) is one when i equals j and zero otherwise. Here M_{n,k}(t,s) counts Motzkin paths with horizontal weight s on the axis and t above it. Moving the three-term recurrence across the pairing yields the column identities, and triangularity of the Motzkin array yields orthogonality.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnTransfer.column_moments`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs](CiglerMotzkinColumnDefs.md)
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal](CiglerMotzkinHankelOrthogonal.md)
