# Boundary-Weighted Motzkin Hankel Series

## Abstract

Boundary-weighted Motzkin paths determine Hankel series over the integer polynomial ring in t and s.

**Definition 1.1 (The coefficient ring).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.Base`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.Base` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

The coefficient ring is the integer polynomial ring in two independent indeterminates t and s, indexed by zero and one respectively.

**Definition 1.2 (The horizontal weight above the axis).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.tVar`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.tVar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

The indeterminate t is the variable indexed by zero in the coefficient ring. It weights horizontal steps at positive height.

**Definition 1.3 (The horizontal weight on the axis).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.sVar`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.sVar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

The indeterminate s is the variable indexed by one in the coefficient ring. It weights horizontal steps at height zero.

**Definition 1.4 (Boundary-weighted Motzkin polynomials).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.motzkin`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.motzkin` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For nonnegative integers n and k, M_{n,k}(t,s) sums the weights of paths from (0,0) to (n,k) with steps (1,1), (1,0) and (1,-1), never below the axis. Up and down steps have weight one; horizontal steps have weight s on the axis and t above it. Initially M_{0,0} = 1 and M_{0,k} = 0 for positive k. The last-step recurrence is M_{n+1,k} = M_{n,k-1} + w_k M_{n,k} + M_{n,k+1}, with the first term omitted at k = 0, w_0 = s and w_k = t for positive k.

**Definition 1.5 (Shifted Hankel determinants).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.hankelDet`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.hankelDet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For nonnegative integers m and n, d_m(n,t,s) is the determinant of the n by n matrix whose entry in row i and column j is M_{m+i+j,0}(t,s), with i and j ranging from zero to n minus one. The determinant of the empty matrix is one.

**Definition 1.6 (Lucas-type polynomials).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.lucas`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.lucas` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

The polynomials L_r(t) satisfy L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r for every nonnegative integer r.

**Definition 1.7 (The denominator factors).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.factorA`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.factorA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

As polynomials in x over the coefficient ring, A_{0,0}(x,t) = 1 - x and A_{0,r}(x,t) = 1 - L_r(t)x + x squared for every positive integer r.

**Definition 1.8 (The specified denominator).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.denominator`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.denominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every nonnegative integer m, Q_m(x,t) is the product of A_{0,m-2j}(x,t) raised to the exponent 1 + j(m-j), over integers j from zero through the integer part of m divided by two.

**Definition 1.9 (Cigler's boundary-weighted Hankel identity).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.claim`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every integer m at least one, there is a polynomial R_m(x,t,s) with integer coefficients such that R_m = Q_m times the formal series summing d_m(n,t,s)x^n over all nonnegative integers n, and the degree of R_m in x is exactly binom(m+1,3) + 1. The identity is an equality of formal power series over the integer polynomial ring in t and s. It is Conjecture 2.1, equation (2.3), of Cigler's paper.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.Base`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.denominator`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.factorA`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.hankelDet`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.lucas`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.motzkin`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.sVar`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.tVar`
