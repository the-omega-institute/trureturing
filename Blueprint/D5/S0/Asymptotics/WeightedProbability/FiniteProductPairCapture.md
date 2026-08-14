# Finite Product Pair Capture Law

## Abstract

Distinct captured rows have the exact second-order weighted intersection mass.

**Theorem 1.1 (Exact two-row weighted capture probability).**

$$(\forall b,\ \sum_{y} q_{b}(y) = 1) \Rightarrow \forall a, a',\ a\neq a' \Rightarrow \operatorname{pairCaptureProbability}\left(q, f, a, a'\right) = \operatorname{fixedSquareMass}\left(q, f, a\right) \operatorname{fixedSquareMass}\left(q, f, a'\right) \prod_{b\neq a, b\neq a'} \operatorname{collisionSquareMass}\left(q, f, b\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture.pair_capture_probability_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the selected columns the two captured rows give fixedSquareMass; at every other column they give collisionSquareMass.

These are the source's second-order sums of squared weights, not squares of the one-row masses.

## References

- Truth anchor: `D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture.pair_capture_probability_exact`
- Dependency: [D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture](FiniteProductCapture.md)
