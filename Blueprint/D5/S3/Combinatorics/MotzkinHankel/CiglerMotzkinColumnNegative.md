# The Negative-Index Unit Endpoint

## Abstract

Uniform horizontal weights give a negative-index vanishing interval and a unit determinant at its next endpoint.

**Theorem 1.1 (Vanishing and the first unit determinant).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnNegative.negative_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnNegative.negative_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

Let h be nonnegative and let g(y) be monic of degree h over the integer polynomial ring in t. Specialize s to t in the orthogonal polynomials p_r and the backward polynomials b_r, where b_0 = s - t, b_1 = (y - t)b_0 - 1 and b_{r+2} = (y - t)b_{r+1} - b_r. For each gap from one through h, form an h by h coefficient matrix with row polynomial b_{gap-1-i} when i is below gap and p_{i-gap} otherwise, taking remainders modulo g and coefficients of y^j in column j. Its determinant is zero. The matrix with row polynomial b_{h-i} modulo g has determinant (-1)^binom(h+1,2). After specialization b_0 vanishes and b_{r+1} = -p_r, so a zero row gives the gap and reversed monicity gives the endpoint.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnNegative.negative_endpoint`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant](CiglerMotzkinColumnDeterminant.md)
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative](CiglerMotzkinHankelNegative.md)
