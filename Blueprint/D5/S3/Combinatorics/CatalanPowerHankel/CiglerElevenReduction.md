# Mixed Remainder and Coefficient Coordinates

## Abstract

A triangular change of polynomial coordinates separates remainders modulo v from the first d coefficients.

**Theorem 1.1 (The coordinate determinant multiplier).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction.coordinate_change`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction.coordinate_change` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

Let k be a nonnegative integer, let d be a positive integer, let v be a monic rational polynomial of degree k, and let Q_i be any k+d rational polynomials. Form a square matrix with entry [X^j](Q_i mod v) for columns j less than k and entry [X^(j-k)]Q_i for the remaining columns. Its determinant is v(0)^d times the determinant of the coefficient matrix with entry [X^j](Q_i mod (X^d v)) for all columns from zero through k+d-1. Remainders mean polynomial remainders on division by a monic polynomial. The monic basis 1,X,...,X^(k-1),v,Xv,...,X^(d-1)v makes the coordinate transformation block triangular with an identity block and a multiplication block of determinant v(0)^d. No nonzero constant coefficient is required.

## References

- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction.coordinate_change`
- Dependency: [D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenMoments](CiglerElevenMoments.md)
