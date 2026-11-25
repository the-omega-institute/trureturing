# Common Counts of Weighted Multinomial Vectors

## Abstract

A common subvector bounds weighted overlap through a lower-degree diagonal.

Let J be finite, let the weights w(j) be nonnegative, and let c(m) be the multinomial coefficient times the monomial weight of count vector m. Write W for the sum of the weights. For degree p vectors m and n, H(m,n) is the sum of their coordinatewise minima. Write D(k) for the sum of c(l)² over degree k and A(p,k) for the sum of c(m)c(n) over ordered pairs of degree p with H(m,n) at least k.

**Theorem 1.1 (A lower-degree diagonal bounds large common counts).**

$$k \le p \Rightarrow \operatorname{A}\left(p, k\right) \le \operatorname{choose}\left(p, k\right)^{2} \cdot W^{2 \cdot \left(p - k\right)} \cdot \operatorname{D}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteMultinomialOverlap.weighted_overlap_le_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k≤p, any pair counted by A(p,k) contains a common subvector l of degree k. Count each choice of occurrences of l on each side. The multiplicity is the product of the coordinate binomial coefficients. For fixed l, write m=l+u. The product of the weight c(m) and its subvector multiplicity is choose(p,k)c(l)c(u), by canceling the factorials and factoring the weights coordinate by coordinate. Summing over u gives choose(p,k)c(l)W^(p−k). The two sides sum independently, and the sum over l yields the bound.

For the next estimate the weights are immaterial. Given two natural count vectors of degree p and radii r(j)≥ρ≥0, write S for the sum of ((m(j)−n(j))r(j))².

**Theorem 1.2 (The unmatched count bounds the squared frequency scale).**

$$2 \cdot \rho^{2} \cdot \left(p - \operatorname{H}\left(m, n\right)\right) \le S$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/FiniteMultinomialOverlap.weighted_count_difference_sq_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute count differences sum to 2(p−H(m,n)) since each side has degree p. Each count difference is an integer, so its square is at least its absolute value. Multiply each comparison by the square of the common radius lower bound and sum.

In the uniform perturbation model the second estimate bounds the Euclidean scale on pairs with small H, and the first controls the weight of pairs with large H. The fixed zeta ordinates still require a positive-resolution arithmetic bound.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/FiniteMultinomialOverlap.weighted_count_difference_sq_ge`
- Truth anchor: `D5/S3/Fourier/Concentration/FiniteMultinomialOverlap.weighted_overlap_le_diagonal`
- Dependency: [D5/S3/Fourier/Concentration/FiniteSincCollisionMoment](FiniteSincCollisionMoment.md)
