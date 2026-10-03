# Negative-Index Motzkin Determinants

## Abstract

Backward orthogonal polynomials determine the vanishing interval and first nonzero determinant at negative indices.

**Definition 1.1 (Backward orthogonal polynomials).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.backward`

*Formalization.* `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.backward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

The polynomials b_r(y) over the integer polynomial ring in t and s satisfy b_0 = s - t, b_1 = (y - t)b_0 - 1 and b_{r+2} = (y - t)b_{r+1} - b_r for every nonnegative integer r. They continue the orthogonal recurrence with b_r corresponding to p_{-r-1}.

**Theorem 1.2 (Vanishing and the first nonzero backward determinant).**

Lean statement: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.negative_determinants`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.negative_determinants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2022). *Some remarks and conjectures about Hankel determinants of polynomials which are related to Motzkin paths*. DOI: [10.48550/arXiv.2204.09910](https://doi.org/10.48550/arXiv.2204.09910). URL: <https://arxiv.org/abs/2204.09910v4>.

*Commentary.*

For every nonnegative integer m and every integer a with 1 at most a and a less than m, the m by m coefficient determinant with row polynomial b_{a-1-i} when i is less than a and p_{i-a} otherwise is zero. Its column j consists of coefficients of y^j. At a = m, (-1)^m times the determinant with row polynomial b_{m-1-i} equals (-1)^binom(m+1,2) times (s - t)^m, and this polynomial is nonzero in the integer polynomial ring in t and s. This nonvanishing concerns independent indeterminates; specialization to s = t can make it zero when m is positive.

## References

- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.backward`
- Truth anchor: `D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.negative_determinants`
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal](CiglerMotzkinHankelOrthogonal.md)
