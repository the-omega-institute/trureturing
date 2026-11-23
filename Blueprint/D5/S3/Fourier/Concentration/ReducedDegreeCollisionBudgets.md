# Collision Budgets from Separation after Cancellation

## Abstract

Separation of low-degree disjoint pairs sharpens the weighted collision budget.

Let J be finite. Use nonnegative weights w(j), radii r(j)≥ρ>0, a base spectrum g, and a closed window at resolution e. Write B(p) for the localized excess budget over ordered distinct degree-p pairs, W for the sum of the weights, and D(p) for the degree-p diagonal mass. Set C=exp(1/2)√(15π/2). The function ofReal maps a real value to its nonnegative part. Fix a positive integer k. When e>0, for each pair u,v of disjoint supports and common degree 0<d<k with d≤p, require the absolute gap between their base frequencies to exceed e+Σ(u(j)+v(j))r(j).

**Theorem 1.1 (Separated residual pairs below degree k contribute zero).**

$$((e \le 0 \lor p < k) \Rightarrow \operatorname{B}\left(p\right) = 0) \land \operatorname{B}\left(p\right) \le \operatorname{ofReal}\left((W^{2 \cdot p}-\operatorname{D}\left(p\right)) \cdot \operatorname{min}\left(\operatorname{min}\left(1, \frac{e}{\rho}\right), \frac{C \cdot e}{\rho \cdot \operatorname{sqrt}\left(2 \cdot k\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets.localized_excess_le_of_reduced_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a pair m,n, subtract their coordinatewise minimum from both vectors. The signed frequency difference is preserved. The residuals have disjoint supports, so their coordinate sum equals the original absolute differences and gives the same drift bound. A reachable distinct pair therefore has reduced degree at least k and Euclidean scale at least ρ√(2k). The multinomial theorem gives the distinct-pair mass W^(2p)−D(p).

When e≤0 the localized budget vanishes. At k=1 the separation hypothesis is vacuous. When k>p, every distinct pair is excluded. The premise is a positive-resolution arithmetic condition on the base spectrum. Its validity for the fixed zeta ordinates at the missing-window parameters is open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets.localized_excess_le_of_reduced_separation`
- Dependency: [D5/S3/Fourier/Concentration/FiniteMultinomialOverlap](FiniteMultinomialOverlap.md)
- Dependency: [D5/S3/Fourier/Concentration/LocalizedCollisionBudgets](LocalizedCollisionBudgets.md)
