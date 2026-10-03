# The Motzkin Orthogonal Polynomial Basis

## Abstract

Monic orthogonal polynomials convert shifted Motzkin Hankel determinants to coefficient determinants of fixed size.

**Definition 1.1 (The orthogonal polynomial recurrence).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.orthogonal`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.orthogonal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Over the integer polynomial ring in t and s, the polynomials p_r(y) are defined by p_0 = 1, p_1 = y - s and p_{r+2} = (y - t)p_{r+1} - p_r for every nonnegative integer r. The variable y is distinct from the parameters t and s.

**Theorem 1.2 (The monic basis expansion).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.orthogonal_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.orthogonal_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every nonnegative integer n, p_n is monic of degree n, and y^n is the sum of M_{n,k}(t,s)p_k(y) over k from zero through n. Thus the Motzkin array gives the change of basis from these polynomials to monomials.

**Theorem 1.3 (The coefficient determinant formula).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.hankelDet_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.hankelDet_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For all nonnegative integers m and n, d_m(n,t,s) equals (-1)^(mn) times the determinant of the m by m matrix whose row i and column j entry is the coefficient of y^j in p_{n+i}(y), with both indices ranging from zero to m minus one. The matrix size is the shift m, independently of the Hankel matrix size n.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.hankelDet_coefficients`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.orthogonal`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.orthogonal_basis`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelTransfer](CiglerMotzkinHankelTransfer.md)
