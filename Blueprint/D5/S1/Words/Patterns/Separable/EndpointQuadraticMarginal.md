# Quadratic discrepancy tails for the actual cycle stream

## Abstract

An explicit quadratic scale controls the shifted discrepancy of every actual marked-cycle prefix.

For each integer initial offset e, natural prefix length j, and tolerance delta > 0, let T(e,j,delta) be the actual stream mass of the event where the absolute value of e plus the first j discrepancy advances strictly exceeds (|e| + max(1,20/delta)^2)(j+1)^2.

**Theorem 1.1 (Explicit uniform marginal bound).**

$$\operatorname{T}\left(e, j, delta\right) \le \operatorname{ofReal}\left(delta\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointQuadraticMarginal.actual_uniform_quadratic_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a scale s in [0,1], the Schröder recurrence gives the shape generating function B(s) and the exact squared deficit (b-B(s))^2 = rho(1-s)(1+B(s)). After grouping the actual cycle by its fixed removal count and terminal sign, its size generating function is (B(s)+rho s)/(1-B(s)).

Each absolute discrepancy advance is at most its cycle size. A deterministic inequality for one minus a product, applied to the discount factors of the first j sizes, bounds the tail using only their coordinate marginals. The bound is uniform in j and does not use independence between diagonal hits.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointQuadraticMarginal.actual_uniform_quadratic_marginal`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit](EndpointFirstCycleHitLimit.md)
