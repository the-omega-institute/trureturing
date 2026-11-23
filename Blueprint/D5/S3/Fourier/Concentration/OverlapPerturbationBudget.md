# A Diagonal Bound for the Sum of Inverse Scales

## Abstract

A common-count threshold bounds the total weight divided by Euclidean scales.

On a finite set J, let w(j)≥0 and r(j)≥ρ>0. Write W for the sum of the weights and c(m) for the weighted multinomial coefficient of m. For a natural degree p, write I(p) for the sum of c(m)c(n)/√S(m,n) over distinct ordered pairs of degree p, where S(m,n)=Σ((m(j)−n(j))r(j))². Define D(k) as the sum of c(l)² over degree k and A(k)=choose(p,k)² W^(2(p−k))D(k). Put T=W^(2p), L=ρ√(2(p−k+1)), and U=ρ√2.

**Theorem 1.1 (The inverse-scale sum is bounded using a lower-degree diagonal).**

$$k \le p \Rightarrow \operatorname{I}\left(p\right) \le \frac{T-\operatorname{D}\left(p\right)}{L} + (\operatorname{min}\left(\operatorname{A}\left(k\right), T\right)-\operatorname{D}\left(p\right)) \cdot (\frac{1}{U}-\frac{1}{L})$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/OverlapPerturbationBudget.weighted_inverse_scale_le_of_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct equal-degree vectors have common count H<p, so the Euclidean scale is at least ρ√2. When H<k, it is at least L. Charge 1/L to every distinct pair and add 1/U−1/L only for pairs with H≥k. Their total weight is bounded by both A(k) and T before removing the diagonal of mass D(p). At k=0 the correction applies to every distinct pair, and at k=p the two scale bounds agree.

For the finite product of independent uniform interval perturbations, the Euclidean-scale affine bound multiplies each inverse scale by exp(1/2)√(15π/2) times the closed resolution. The corresponding weighted perturbation budget is bounded by the displayed right side times this factor. Fixed zeta ordinates still need an arithmetic bound at positive resolution.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/OverlapPerturbationBudget.weighted_inverse_scale_le_of_overlap`
