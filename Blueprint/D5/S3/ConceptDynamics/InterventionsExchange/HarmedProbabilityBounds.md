# Harmed Probability Bounds

## Abstract

The harmed potential-outcome probability has the sharp marginal bounds.

**Theorem 1.1 (The harmed probability lies between both marginal bounds).**

$$\forall \mu: \operatorname{Measure}(\operatorname{Bool} \times \operatorname{Bool}), [\operatorname{IsProbabilityMeasure}(\mu)] \Rightarrow (\operatorname{max}(0, \mu(Y0 = 1) - \mu(Y1 = 1)) \leq \mu(Y0 = 1 \land Y1 = 0) \land \mu(Y0 = 1 \land Y1 = 0) \leq \operatorname{min}(\mu(Y0 = 1), 1 - \mu(Y1 = 1))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InterventionsExchange/HarmedProbabilityBounds.harmed_probability_frechet_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A probability measure on the pair of Boolean potential outcomes supplies the two marginal event probabilities and the joint event in which the first outcome is true while the second is false.

The joint harmed event is contained in the first marginal and in the complement of the second. The first marginal is contained in the union of the harmed event and the second marginal, which gives the lower bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InterventionsExchange/HarmedProbabilityBounds.harmed_probability_frechet_bound`
