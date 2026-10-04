# Cigler's Boundary-Weighted Motzkin Hankel Formula

## Abstract

Cigler's boundary-weighted Motzkin Hankel series has the specified denominator and a numerator of exact degree binom(m+1,3) + 1 for every positive shift m.

**Theorem 1.1 (The boundary-weighted generating function).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-boundary-motzkin-hankel` (proved) by `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-boundary-motzkin-hankel","declaration_gid":"D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every integer m at least one, let M_{n,k}(t,s) sum the weights of Motzkin paths from (0,0) to (n,k) never below the axis, with up and down steps weighted one, horizontal steps on the axis weighted s, and horizontal steps above it weighted t. Put d_m(n,t,s) = det(M_{m+i+j,0}(t,s)) for indices i and j from zero to n minus one. Define L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r, and set A_{0,0}(x,t) = 1 - x and A_{0,r}(x,t) = 1 - L_r(t)x + x squared for positive r. There is an integer polynomial R_m(x,t,s) of exact x-degree binom(m+1,3) + 1 such that the formal series summing d_m(n,t,s)x^n over all nonnegative n, multiplied by the product of A_{0,m-2j}(x,t)^(1+j(m-j)) for j from zero through the integer part of m divided by two, equals R_m. This establishes Conjecture 2.1, equation (2.3), of Cigler's paper. Orthogonal coefficient determinants and their two reciprocal branches give polynomial factors of degree at most j(m-j) in the index n. Alternant confluence gives the denominator exponents, and the first nonzero negative-index determinant fixes the numerator degree. The identity holds over the integer polynomial ring in t and s, so it remains valid under specialization, including repeated reciprocal roots. The exact degree is asserted over that ring; specialization can lower it. The denominator is the specified common denominator, without an assertion that the numerator is relatively prime to it.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.result`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelConfluence](CiglerMotzkinHankelConfluence.md)
