# Cigler's Partial Theta Hankel Determinant Conjecture

## Abstract

Every normalized backward-shifted partial theta Hankel quotient is a monic integer polynomial with the conjectured degree and values at zero and one.

**Theorem 1.1 (The normalized quotient formula for all shifts).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankel.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For every pair of nonnegative integers m and n, D_{0,n+1}(q) is nonzero, and there exists a polynomial r_{m,n}(q) with integer coefficients satisfying D_{-m,n+m+1}(q) = (-1)^{binom(m + 1, 2)} r_{m,n}(q) q^{m binom(n, 2)} D_{0,n+1}(q). The polynomial r_{m,n} is monic, has degree mn(n + m + 2)/2, and satisfies r_{m,n}(1) = 1 and r_{m,n}(0) = (-1)^{mn}. Here D_{-m,N}(q) is the determinant with entries a(-m + i + j, q), where a(s, q) is q^{binom(s, 2)} for nonnegative s and zero otherwise. Integral alternant division gives the polynomial quotient; the extremal determinant terms give monicity, degree, and the value at zero; coalescence and the staircase Pascal determinant give the value at one. These identities prove the conjecture following equation (2) in Section 1 of Cigler's paper.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankel.result`
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelCoalescence](PartialThetaHankelCoalescence.md)
