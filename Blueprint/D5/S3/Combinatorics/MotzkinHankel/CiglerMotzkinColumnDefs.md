# Motzkin-Column Hankel Series

## Abstract

Uniform horizontal weights define the Hankel series of every Motzkin-triangle column and Cigler's specified denominator.

**Definition 1.1 (Uniform horizontal weights).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.specialize`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.specialize` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

The integer algebra homomorphism from the polynomial ring in t and s to the integer polynomial ring in t sends both indeterminates to t. Thus every horizontal step has weight t, including steps on the axis.

**Definition 1.2 (Column Hankel determinants).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnHankel`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnHankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For nonnegative integers k, m and n, d_m^{(k)}(n,t) is the determinant of the n by n matrix with entry M_{m+i+j,k}(t) in row i and column j, for indices from zero to n minus one. Here M_{r,k}(t) sums the weights of Motzkin paths from (0,0) to (r,k) never below the axis, with up and down steps of weight one and horizontal steps of weight t. The empty determinant is one.

**Definition 1.3 (Signed Lucas factors).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnFactor`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnFactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Put e = (-1)^binom(k+1,2). As polynomials in x over the integer polynomial ring in t, A_{k,0}(x,t) = 1 - e x^(k+1), and A_{k,r}(x,t) = 1 - e L_r(t)x^(k+1) + x^(2(k+1)) for positive r. The Lucas polynomials satisfy L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r. These are the factors in equation (1.28) of Cigler's paper.

**Definition 1.4 (The specified common denominator).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnDenominator`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For nonnegative integers k and m, Q_m^{(k)}(x,t) is the product of A_{k,(k+1)(m-2j)}(x,t) raised to the exponent 1 + j(m-j), over j from zero through the integer part of m divided by two.

**Definition 1.5 (Cigler's column identity).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.claim`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every nonnegative integer k and every integer m at least one, there is an integer polynomial R_m^{(k)}(x,t) such that R_m^{(k)} equals Q_m^{(k)} times the formal series summing d_m^{(k)}(n,t)x^n over all nonnegative n. Its degree in x is exactly binom(m+1,3) + k(binom(m,1) + binom(m,2) + binom(m,3)). This is Conjecture 1.3, equation (1.30), of Cigler's paper. The degree is over the integer polynomial ring in t; specializing t can lower it. The identity does not assert that numerator and denominator are relatively prime.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnDenominator`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnFactor`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.columnHankel`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.specialize`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs](CiglerMotzkinHankelDefs.md)
