# Shifted Hankel Determinants of Catalan Powers

## Abstract

Odd powers of the Catalan generating function determine shifted Hankel determinants with a conjectured closed form.

**Definition 1.1 (The Catalan power coefficients).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.catalanPowerCoeff`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.catalanPowerCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a nonnegative integer r and an integer j, define the rational number C_{r,j} to be r/(2j+r) times binom(2j+r,j) when j is nonnegative, and zero when j is negative. Division by zero gives zero. For positive r, these are the coefficients of the r-th power of the Catalan generating function c(x).

**Definition 1.2 (The shifted Hankel determinant).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.shiftedHankel`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.shiftedHankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a nonnegative integer r, an integer shift s and a nonnegative integer N, define D_{r,s}(N) as the determinant of the N by N matrix with entry C_{r,i+j+s} in row i and column j, where both indices range from zero through N minus one. The determinant of the empty matrix is one, and negative coefficient indices contribute zero.

**Definition 1.3 (The odd-power determinant formula).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.claim`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

Conjecture 11 asserts that for every integer k at least one, every integer m from zero through k+1, and every nonnegative integer n, D_{2k+1,m-k+1}((2k+1)n+k) = (-1)^(kn+binom(k,2)) (2k+1)^m (n+1)^m. The shift m-k+1 is an integer and may be negative.

## References

- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.catalanPowerCoeff`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs.shiftedHankel`
