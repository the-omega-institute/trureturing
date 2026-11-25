# Finite-to-stream convergence of literal diagonal hits

## Abstract

A fixed number of actual emitted cycles has a literal finite diagonal-hit probability converging to the marked-stream law.

Fix a natural number k and an integer e. Write p(n) for the uniform mass among size-n avoiders of the event that canonical parsing succeeds through k cycles and some original emitted point satisfies i-pi(i)=e. Write q(k,e) for the first-k hit probability under the actual marked-stream law. Each cycle uses the starting offset plus the lower-value-minus-position advances of the previous cycles.

**Theorem 1.1 (Full-sequence convergence at fixed k and e).**

$$\operatorname{Tendsto}\left(p, atTop, \operatorname{nhds}\left(\operatorname{q}\left(k, e\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit.actualCanonicalFirstKLiteralHit_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bounded successful tuple cells are disjoint and their actual finite probabilities converge to the corresponding stream cylinders. Eventual original-coordinate agreement identifies precisely the selected cells on each side. The same finite family controls the probabilities omitted on both sides; bounding the two complementary masses and the finite-sum error proves convergence over the full sequence.

The statement fixes k and e before taking n to infinity. It is not a growing-k estimate, an occupied lower-quantile bound, a multi-cycle divergence result, or a theorem about the entire permutation's diagonal.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit.actualCanonicalFirstKLiteralHit_limit`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointCanonicalCycle](EndpointCanonicalCycle.md)
