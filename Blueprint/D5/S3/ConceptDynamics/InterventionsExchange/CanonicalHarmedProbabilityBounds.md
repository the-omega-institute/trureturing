# Canonical Harmed Probability Bounds

## Abstract

The canonical harmed event satisfies the sharp bounds from its marginals.

**Theorem 1.1 (The harmed probability lies between its sharp marginal bounds).**

$$\forall \mu: \operatorname{Measure}(\operatorname{Bool} \times \operatorname{Bool}), [\operatorname{IsProbabilityMeasure}(\mu)] \Rightarrow (\operatorname{max}(0, P(Y0 = 1) - P(Y1 = 1)) \leq P(Y0 = 1 \land Y1 = 0) \land P(Y0 = 1 \land Y1 = 0) \leq \operatorname{min}(P(Y0 = 1), 1 - P(Y1 = 1))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/CanonicalHarmedProbabilityBounds.canonical_harmed_probability_frechet_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A probability measure on paired Boolean potential outcomes constructs the first and second marginal events and the harmed event where the first outcome is true and the second is false.

The harmed probability is at least the positive part of the marginal difference and at most both the first marginal and the complement of the second marginal.

The proof imports and applies the frozen family theorem on these exact measure-theoretic primitives; it introduces no second event model.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/CanonicalHarmedProbabilityBounds.canonical_harmed_probability_frechet_bound`
- Dependency: [D5/S3/ConceptDynamics/InterventionBounds/HarmedProbabilityBounds](../InterventionBounds/HarmedProbabilityBounds.md)
