# The Lowest Term of the Shifted Hankel Determinant

## Abstract

The reverse permutation gives the unique lowest-degree nonzero term of the backward-shifted Hankel determinant.

**Theorem 1.1 (The first nonzero coefficient).**

Lean statement: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest.lowest_term`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest.lowest_term` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2024). *Hankel determinants of backward shifts of the coefficients of a partial theta function*. DOI: [10.48550/arXiv.2407.05768](https://doi.org/10.48550/arXiv.2407.05768). URL: <https://arxiv.org/abs/2407.05768v2>.

*Commentary.*

For every pair of nonnegative integers m and n, every coefficient of D_{-m,n+m+1}(q) below degree (m + n + 1) binom(n, 2) vanishes, and the coefficient at that degree is (-1)^{binom(m + n + 1, 2)}. A determinant term can be nonzero only when its permutation sends each index i to an index j with i + j at least m. Among these permutations, the full reversal uniquely minimizes the sum of binom(i + j - m, 2). Its sign is the displayed coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/PartialTheta/PartialThetaHankelLowest.lowest_term`
- Dependency: [D5/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde](PartialThetaHankelVandermonde.md)
