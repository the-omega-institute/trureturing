# Polynomial Identities for the Residue Reduction

## Abstract

Chebyshev product identities control periodic remainders, reflection and paired rows of the Catalan moment polynomials.

**Theorem 1.1 (Periodicity, reflection and monic quotients).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials.polynomial_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials.polynomial_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

Let p_j and h_j be the boundary-weighted Motzkin orthogonal polynomials specialized to interior weight two and boundary weights one and three respectively. Thus p_0 = h_0 = 1, p_1 = X-1, h_1 = X-3, and each family satisfies q_{j+2} = (X-2)q_{j+1}-q_j. Write C_0 = 2, C_1 = X and S_0 = 1, S_1 = X for the Chebyshev families satisfying q_{j+2} = Xq_{j+1}-q_j. For all nonnegative k and j, p_{2k+1+j}-p_j = p_k C_{k+j+1}(X-2). For every nonnegative s at most k, p_{k+s}+p_{k-s} = p_k C_s(X-2). For every positive B and every nonnegative t less than B, p_{B+t}+p_{B-1-t} = X S_{B-1}(X-2) h_t. The recurrence gives p_j = S_j(X-2)+S_{j-1}(X-2) and h_j = S_j(X-2)-S_{j-1}(X-2), with S_{-1} = 0. The product identity C_m S_r = S_{r+m}+S_{r-m} and the identity C_{t+1}(X-2)+C_t(X-2) = Xh_t yield the three formulas.

## References

- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials.polynomial_structure`
- Dependency: [D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenReduction](CiglerElevenReduction.md)
