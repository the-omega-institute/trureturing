# The Unshifted Partial Theta Hankel Determinant

## Abstract

A Vandermonde product evaluates the unshifted Hankel determinant and establishes its nonvanishing.

**Theorem 1.1 (The unshifted determinant formula).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde.unshifted`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde.unshifted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For every nonnegative integer n, put V_n(q) = product over d from one through n of (q^d - 1)^{n + 1 - d}. Then D_{0,n+1}(q) = q^{(n + 1) binom(n, 2)} V_n(q), and this determinant is nonzero. The polynomial V_n is monic, has degree binom(n + 2, 3), and satisfies V_n(0) = (-1)^{binom(n + 1, 2)}. Empty products are one. Extracting the row and column monomials leaves the Vandermonde matrix at 1, q, through q^n; grouping its factors by the difference of the two indices gives the displayed product.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde.unshifted`
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs](PartialThetaHankelDefs.md)
