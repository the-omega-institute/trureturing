# Coalescence and the Staircase Pascal Determinant

## Abstract

Coalescing alternant variables at one yields a binomial determinant, and a staircase specialization evaluates it.

**Theorem 1.1 (The staircase determinant).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.staircase_det`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.staircase_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For all nonnegative integers m and n, form a square integer matrix of size m + n + 1, with row and column indices beginning at zero. In row i below m its entry in column j is one when m - i is at most j and zero otherwise. In row i at least m its entry is binom(j, i - m). The determinant is (-1)^{binom(m + 1, 2)}. Finite differences of the binomial rows give a Pascal determinant of value one, while the staircase rows contribute the stated sign.

**Theorem 1.2 (Evaluation of a divided alternant at one).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.coalescence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.coalescence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For nonnegative integers m and c, choose any m by (m + c) matrix T with integer entries and any integer polynomial B in variables x_0 through x_{c-1}. Form the square matrix A of size m + c whose first m rows are T and whose row m + k has entry x_k^j in column j. Suppose det A equals product over 0 at most u less than v below c of (x_v - x_u), multiplied by B. Then B(1, through 1) equals the determinant of the integer matrix with the same first m rows T and with entry binom(j, k) in row m + k and column j. Expansion at x_k = 1 identifies the first alternating homogeneous component with this binomial determinant; the identity also includes c = 0.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.coalescence`
- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence.staircase_det`
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest](PartialThetaHankelHighest.md)
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient](PartialThetaHankelQuotient.md)
