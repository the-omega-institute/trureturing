# A Diagonal Bound for the Sum of Inverse Scales

## Abstract

A common-count threshold bounds the total weight divided by Euclidean scales.

On a finite set J, let w(j)≥0 and r(j)≥ρ>0. Write W for the sum of the weights and c(m) for the weighted multinomial coefficient of m. For a natural degree p, write I(p) for the sum of c(m)c(n)/√S(m,n) over distinct ordered pairs of degree p, where S(m,n)=Σ((m(j)−n(j))r(j))². Define D(k) as the sum of c(l)² over degree k and A(k)=choose(p,k)² W^(2(p−k))D(k).

**Theorem 1.1 (The inverse-scale sum is bounded using a lower-degree diagonal).**

$$k \le p \Rightarrow \operatorname{I}\left(p\right) \le \frac{W^{2 \cdot p}}{\rho \cdot \operatorname{sqrt}\left(2 \cdot \left(p - k + 1\right)\right)} + \frac{\operatorname{A}\left(k\right)}{\rho \cdot \operatorname{sqrt}\left(2\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/OverlapPerturbationBudget.weighted_inverse_scale_le_of_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct equal-degree vectors have common count H<p, so the Euclidean scale is at least ρ√2. When H<k, it is at least ρ√(2(p−k+1)). Bound the weight of pairs below the threshold by W^(2p) and the weight of pairs at or above it by A(k). Both bounds refer to the same weighted ordered pairs.

For the finite product of independent uniform interval perturbations, the Euclidean-scale affine bound multiplies each inverse scale by exp(1/2)√(15π/2) times the closed resolution. The corresponding weighted perturbation budget is bounded by the displayed right side times this factor. Fixed zeta ordinates still need an arithmetic bound at positive resolution.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/OverlapPerturbationBudget.weighted_inverse_scale_le_of_overlap`
