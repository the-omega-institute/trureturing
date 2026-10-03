# Mixed Reciprocal Branches and Grouped Recurrences

## Abstract

Same-branch pairs bound the polynomial degrees in mixed determinants, and common power classes give a step-sized recurrence.

**Theorem 1.1 (Polynomial coefficients of mixed branches).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches.mixed_branch_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches.mixed_branch_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let K be a field of characteristic zero, let u_i(y) be invertible formal series indexed by a finite set of size N, and let a_i(y) and b_i(y) be arbitrary formal series. Choose a subset Z of size m on which every u_i has the same nonzero constant coefficient alpha. There are polynomials P_S over K, one for each subset S of the indices, of natural degree at most j(m-j), where j is the size of Z intersect S. For every integer n, the coefficient of y^binom(m,2) in the determinant with entry a_i u_i^(n+r) + b_i u_i^(-n-r) in row r and column i equals the sum of beta_S^n P_S(n) over all S. Here beta_S is the constant coefficient of the product of u_i inverse for i in S and u_i for i outside S. Same-branch pairs within Z supply the vanishing factors that give the degree bound.

**Theorem 1.2 (A recurrence for common power classes).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches.grouped_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches.grouped_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let K be a field of characteristic zero, let I and J be finite index types, and let d be a positive integer. Choose nonzero rho_i and mu_j with rho_i^d = mu_{index(i)}, polynomials P_i, and nonnegative exponents e_j such that the natural degree of P_i is strictly below e_{index(i)}. Put Q(x) equal to the product over j of (1 - mu_j x^d)^e_j, and put v(n) equal to the sum over i of rho_i^n P_i(n). For every integer n, the sum of Q_l v(n-l) over l from zero through the degree of Q is zero, where Q_l is its coefficient of x^l. A d-step difference lowers the polynomial degree of each mode in its power class.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches.grouped_recurrence`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnBranches.mixed_branch_coefficients`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant](CiglerMotzkinColumnDeterminant.md)
