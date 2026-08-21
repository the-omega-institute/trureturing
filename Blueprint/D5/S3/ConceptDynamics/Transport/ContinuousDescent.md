# Continuous Descent

## Abstract

A continuous fiber-constant map descends uniquely through a quotient map.

**Theorem 1.1 (Continuous maps descend uniquely through quotient maps).**

$$\forall X, B, Y: \operatorname{Type},\\{}[\operatorname{TopologicalSpace}(X)], [\operatorname{TopologicalSpace}(B)], [\operatorname{TopologicalSpace}(Y)],\\{}q: \operatorname{ContinuousMap}(X, B), T: \operatorname{ContinuousMap}(X, Y),\\{}\operatorname{IsQuotientMap}(q), \operatorname{FactorsThrough}(T, q),\\{}\exists! \overline{T}: \operatorname{ContinuousMap}(B, Y), T = \overline{T} \circ q.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Transport/ContinuousDescent.continuous_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a quotient map from X onto B, and let T be a continuous map from X to Y that is constant on every fiber of q.

There is exactly one continuous map from B to Y whose composition with q is T. This is the continuous descent asserted by the formal-concept-dynamics source atom.

Pinned Mathlib supplies IsQuotientMap.lift for existence, lift_comp for the commuting triangle, and ContinuousMap.cancel_right for uniqueness from surjectivity. The Lean theorem is a thin wrapper around those declarations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Transport/ContinuousDescent.continuous_descent`
