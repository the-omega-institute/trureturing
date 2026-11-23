# Collision Budgets from Separation after Cancellation

## Abstract

Separation of low-degree disjoint pairs sharpens the weighted collision budget.

Let J be finite. Use nonnegative weights w(j), radii r(j)≥ρ>0, a base spectrum g, and a closed window of radius e≥0. Write B(p) for the localized excess budget over ordered distinct degree-p pairs, W for the sum of the weights, and D(p) for the degree-p diagonal mass. Set C=exp(1/2)√(15π/2).

**Theorem 1.1 (Separated residual pairs below degree k contribute zero).**

$$(p < k \Rightarrow \operatorname{B}\left(p\right) = 0) \land \operatorname{B}\left(p\right) \le (W^{2 \cdot p}-\operatorname{D}\left(p\right)) \cdot \operatorname{min}\left(1, \frac{C \cdot e}{\rho \cdot \operatorname{sqrt}\left(2 \cdot k\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets.localized_excess_le_of_reduced_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive integer k. For every pair u,v of common degree 0<d<k with disjoint supports, require the absolute gap between their base frequencies to exceed e+Σ(u(j)+v(j))r(j). The strict inequality excludes reach even at the endpoints of the closed band.

For a pair m,n, subtract their coordinatewise minimum from both vectors. The signed frequency difference is preserved. The residuals have disjoint supports, so their coordinate sum equals the original absolute differences and gives the same drift bound. A reachable distinct pair therefore has reduced degree at least k and Euclidean scale at least ρ√(2k). The multinomial theorem gives the distinct-pair mass W^(2p)−D(p).

When k=1 the separation hypothesis is vacuous. When k>p, every distinct pair is excluded. The premise is a positive-resolution arithmetic condition on the base spectrum. Its validity for the fixed zeta ordinates at the missing-window parameters is open.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/ReducedDegreeCollisionBudgets.localized_excess_le_of_reduced_separation`
- Dependency: [D5/S3/Fourier/Concentration/FiniteMultinomialOverlap](FiniteMultinomialOverlap.md)
- Dependency: [D5/S3/Fourier/Concentration/LocalizedCollisionBudgets](LocalizedCollisionBudgets.md)
