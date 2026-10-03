# Cigler's Motzkin-Column Hankel Formula

## Abstract

At every positive shift, each Motzkin-triangle column has Cigler's specified Hankel-series denominator and a numerator of the exact stated degree.

**Theorem 1.1 (The generating function of a Motzkin-column Hankel determinant).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-motzkin-column-hankel` (proved) by `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-motzkin-column-hankel","declaration_gid":"D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every nonnegative integer k and every integer m at least one, let M_{n,k}(t) sum the weights of Motzkin paths from (0,0) to (n,k) never below the axis, with up and down steps of weight one and all horizontal steps of weight t. Put d_m^{(k)}(n,t) = det(M_{m+i+j,k}(t)) for indices i and j from zero to n minus one, with empty determinant one. Define L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r, and put e = (-1)^binom(k+1,2). Set A_{k,0}(x,t) = 1 - e x^(k+1) and A_{k,r}(x,t) = 1 - e L_r(t)x^(k+1) + x^(2(k+1)) for positive r. There is an integer polynomial R_m^{(k)}(x,t) of exact x-degree binom(m+1,3) + k(binom(m,1) + binom(m,2) + binom(m,3)) such that the formal series summing d_m^{(k)}(n,t)x^n over all nonnegative n, multiplied by the product of A_{k,(k+1)(m-2j)}(x,t)^(1+j(m-j)) over j from zero through the integer part of m divided by two, equals R_m^{(k)}. This establishes Conjecture 1.3, equation (1.30), of Cigler's paper. Monic remainder determinants give a mixed alternant with m confluent nodes and k fixed Chebyshev nodes. Reciprocal branches bound its polynomial modes by j(m-j), and the first nonzero negative-index determinant fixes the numerator degree. The identity holds over the integer polynomial ring in t and therefore under every specialization of t. The exact degree is asserted over that ring; specialization can lower it. The specified denominator is a common denominator, without an assertion that numerator and denominator are relatively prime.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.result`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnSequence](CiglerMotzkinColumnSequence.md)
