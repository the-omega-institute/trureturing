# The Extremal Coefficients of the Hankel Quotient

## Abstract

The extremal determinant terms determine the degree, leading coefficient, and constant coefficient of every normalized quotient.

**Theorem 1.1 (Degree and extremal coefficients).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest.quotient_data`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest.quotient_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For all nonnegative integers m and n and every polynomial r(q) with integer coefficients satisfying D_{-m,n+m+1}(q) = (-1)^{binom(m + 1, 2)} r(q) q^{m binom(n, 2)} D_{0,n+1}(q), the polynomial r is monic, has degree mn(n + m + 2)/2, and satisfies r(0) = (-1)^{mn}. The unique maximal-degree determinant term comes from the permutation that reverses the indices zero through m and fixes the remaining indices. Its coefficient and degree, compared with those of the normalizing factors, give the leading coefficient and degree of r. The lowest nonzero determinant coefficient gives its constant coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest.quotient_data`
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest](PartialThetaHankelLowest.md)
