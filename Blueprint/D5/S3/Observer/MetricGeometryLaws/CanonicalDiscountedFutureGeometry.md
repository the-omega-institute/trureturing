# Canonical Discounted Future Geometry

## Abstract

Discounted future distance is the canonical bounded-observer pseudometric.

**Theorem 1.1 (Discounted future distance gives the observer pseudometric).**

$$0 < gamma < 1 \land \operatorname{BoundedOutputMetric}\left(q, B\right) \Rightarrow\\\exists Dgamma, \operatorname{CanonicalDiscountedDistance}\left(Dgamma, F, q, gamma\right) \land \operatorname{PseudoMetric}\left(Y, Dgamma\right) \land\\\forall x, y\in Y,\\{}\operatorname{d}\left(\operatorname{q}\left(x\right), \operatorname{q}\left(y\right)\right) \leq \operatorname{Dgamma}\left(x, y\right) \land\\\operatorname{Dgamma}\left(\operatorname{F}\left(x\right), \operatorname{F}\left(y\right)\right) \leq gamma^{-1} \operatorname{Dgamma}\left(x, y\right) \land\\\operatorname{LipschitzWith}\left(gamma^{-1}, F, Dgamma\right) \land\\(\operatorname{Dgamma}\left(x, y\right) = 0) \iff \operatorname{KInfinity}\left(x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry.canonical_discounted_future_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a deterministic state update and q a readout into a bounded metric space. For a discount gamma strictly between zero and one, D_gamma is the supremum of gamma^n times the output distance after n updates.

The existing Bellman equation supplies both current-output domination and the one-step gamma-inverse contraction. The latter is also packaged as the standard Mathlib LipschitzWith predicate.

Strict positivity of every discount power makes zero D_gamma equivalent to equality of every finite future readout, namely membership in the infinite-future relation K_infty.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry.canonical_discounted_future_geometry`
- Dependency: [D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric](DiscountedPredictionPseudometric.md)
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../Separation/FiniteFutureCongruence.md)
