# Partial Theta Coefficients and Hankel Determinants

## Abstract

Backward shifts of partial theta coefficients define Hankel determinants and their normalized polynomial quotients.

**Definition 1.1 (The partial theta coefficient).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.coeffA`

*Formalization.* `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.coeffA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For every integer s, a(s, q) is q^{binom(s, 2)} when s is nonnegative and zero when s is negative. It is a polynomial in q with integer coefficients. These are the coefficients of the partial theta series summed over nonnegative s of q^{binom(s, 2)} x^s, extended by zero to negative indices.

**Definition 1.2 (The backward-shifted Hankel determinant).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.hankel`

*Formalization.* `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.hankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For nonnegative integers m and N, D_{-m,N}(q) is the determinant of the N by N matrix with entry a(-m + i + j, q) in row i and column j, where i and j range from zero through N - 1. The determinant is a polynomial in q with integer coefficients; the determinant of the empty matrix is one.

**Definition 1.3 (The normalized quotient conjecture).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.claim`

*Formalization.* `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For every pair of nonnegative integers m and n, D_{0,n+1}(q) is nonzero and there exists a polynomial r_{m,n}(q) with integer coefficients such that D_{-m,n+m+1}(q) = (-1)^{binom(m + 1, 2)} r_{m,n}(q) q^{m binom(n, 2)} D_{0,n+1}(q). This polynomial is monic, has degree mn(n + m + 2)/2, and satisfies r_{m,n}(1) = 1 and r_{m,n}(0) = (-1)^{mn}. This is the conjecture following equation (2) in Section 1 of Cigler's paper, together with nonvanishing of the unshifted determinant.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.coeffA`
- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.hankel`
