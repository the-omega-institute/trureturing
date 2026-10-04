# An Integral Quotient for the Shifted Determinant

## Abstract

Integral division of an augmented alternant constructs the normalized shifted Hankel quotient.

**Theorem 1.1 (Integral alternant division).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient.integral_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient.integral_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For nonnegative integers m and n, set N = n + m + 1. There exists r(q) in the integer polynomial ring such that D_{-m,N}(q) = (-1)^{binom(m + 1, 2)} r(q) q^{m binom(n, 2)} D_{0,n+1}(q). More precisely, form an N by N matrix A over the polynomial ring in x_0 through x_n with coefficients in the integer polynomial ring in q. For row i below m, its entry in column j is zero if j is below m - i and is q^{binom(m - i + 1, 2) + (m - i)(N - j)} otherwise. For row i at least m, its entry is x_{i-m}^j. There exists an integral polynomial B with det A = product over 0 at most u less than v at most n of (x_v - x_u), multiplied by B. Set t_i = (m - i)N for i below m and t_i = 0 otherwise. The same r and B satisfy q^{sum_i t_i + N binom(n, 2)} r(q) = (-1)^{binom(m + 1, 2)} q^{sum_j binom(j, 2) + 2 binom(n + 1, 3)} B(1, q, through q^n), where both sums range from zero through N - 1.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient.integral_quotient`
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest](PartialThetaHankelLowest.md)
