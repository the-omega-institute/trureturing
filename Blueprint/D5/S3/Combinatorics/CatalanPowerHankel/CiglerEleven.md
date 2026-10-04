# Cigler's Conjecture 11

## Abstract

The shifted Hankel determinant of an odd Catalan power has Cigler's closed form, including both upper boundary shifts.

**Theorem 1.1 (Truncated multiplication on a monic family).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.coefficient_determinant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.coefficient_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

Let a be a nonnegative integer, let F and g be rational polynomials, and let q_t be monic of degree t for every t less than a. The determinant of the (a+1) by (a+1) coefficient matrix of the ordered polynomials g,XFq_0,...,XFq_{a-1}, in columns of degrees zero through a, equals g(0)F(0)^a. The monic coefficient matrix has determinant one, and truncated multiplication by F is triangular with constant diagonal F(0). The formula permits a = 0 and F(0) = 0.

**Theorem 1.2 (The residue-class determinant).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.residue_determinant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.residue_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For k at least one, m from zero through k+1 and n nonnegative, set N = (2k+1)n+k, B = (2k+1)(n+1) and F = S_{B-1}(X-2), where S_0 = 1, S_1 = X and S_{j+2} = XS_{j+1}-S_j. Let p_0 = 1, p_1 = X-1 and p_{j+2} = (X-2)p_{j+1}-p_j. In a square matrix of size k+m+1, use [X^j](p_{N+i} mod p_k) for columns j less than k and [X^(j-k)]p_{N+i} for the other columns. Its determinant equals (-1)^(binom(k+1,2)+k) p_N(0) F(0)^m. Reversing the first k+1 rows and adding retained rows pairs the last m rows into XFh_t, where h_t is the monic degree-t Motzkin polynomial with interior weight two and boundary weight three. Periodicity and reflection modulo p_k give a triangular first block, and truncated multiplication evaluates the remaining coefficient block. The retained boundary row supplies the final addition when m = k+1.

**Theorem 1.3 (The shifted Hankel formula for odd Catalan powers).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-catalan-power-shifted-hankel` (proved) by `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-catalan-power-shifted-hankel","declaration_gid":"D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For every integer k at least one, every integer m from zero through k+1 and every nonnegative integer n, D_{2k+1,m-k+1}((2k+1)n+k) = (-1)^(kn+binom(k,2)) (2k+1)^m (n+1)^m, where C_{r,j} = r/(2j+r) binom(2j+r,j) for nonnegative j, C_{r,j} = 0 for negative j and D_{r,s}(N) = det(C_{r,i+j+s}) with indices from zero through N-1. The empty determinant is one. This proves Conjecture 11 of Cigler's paper. The specialized boundary-weighted Motzkin orthogonal family supplies monic polynomials p_j of degree j and the normalized Catalan moment dictionary. The determinant reduction for polynomial multipliers in that orthonormal family converts the order-N Hankel determinant to a size-k+m+1 remainder determinant modulo X^(m+1)p_k, with sign (-1)^(N(k+m+1)). The mixed coordinate transformation and the residue-class determinant evaluate it using p_j(0) = (-1)^j and S_{B-1}(-2) = (-1)^(B-1)B for B = (2k+1)(n+1). The resulting parity is kn+binom(k,2). Negative shifts and both cases m = k and m = k+1 are included.

## References

- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.coefficient_determinant`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.residue_determinant`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerEleven.result`
- Dependency: [D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials](CiglerElevenPolynomials.md)
- Dependency: [D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDeterminant](../MotzkinHankel/CiglerMotzkinColumnDeterminant.md)
