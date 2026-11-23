# A Diagonal Bound for the Sum of Inverse Scales

## Abstract

Nested common-count thresholds bound the total weight divided by Euclidean scales.

On a finite set J, let w(j)≥0 and r(j)≥ρ>0. Write W for the sum of the weights and c(m) for the weighted multinomial coefficient of m. For a natural degree p, write I(p) for the sum of c(m)c(n)/√S(m,n) over distinct ordered pairs of degree p, where S(m,n)=Σ((m(j)−n(j))r(j))². Define D(k) as the sum of c(l)² over degree k and A(k)=choose(p,k)² W^(2(p−k))D(k). Put T=W^(2p), Q(h)=1/(ρ√(2(p−h))) for 0≤h<p, and B(h)=min over 0≤i≤h of min(A(i),T), minus D(p). The correction sum is empty for p≤1. At p=0 the result is zero.

**Theorem 1.1 (The inverse-scale sum is bounded using the lower-degree diagonals).**

$$\operatorname{I}\left(p\right) \le (T-\operatorname{D}\left(p\right)) \cdot \operatorname{Q}\left(0\right) + \sum_{0\le h<p-1} \operatorname{B}\left(h + 1\right) \cdot (\operatorname{Q}\left(h + 1\right)-\operatorname{Q}\left(h\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/OverlapPerturbationBudget.weighted_inverse_scale_le_of_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct equal-degree vectors have common count H<p and reciprocal scale at most Q(H). Split Q(H) into Q(0) and its increments up to H. The increment Q(h+1)−Q(h) is charged exactly on the pairs with H≥h+1. Each earlier threshold bounds this nested tail, so take their minimum and subtract the diagonal. All the increments used by the sum are nonnegative.

For the finite product of independent uniform interval perturbations, the Euclidean-scale affine bound multiplies each inverse scale by exp(1/2)√(15π/2) times the closed resolution. The corresponding weighted perturbation budget is bounded by the displayed right side times this factor. Fixed zeta ordinates still need an arithmetic bound at positive resolution.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/OverlapPerturbationBudget.weighted_inverse_scale_le_of_overlap`
- Dependency: [D5/S3/Fourier/Concentration/FiniteMultinomialOverlap](FiniteMultinomialOverlap.md)
