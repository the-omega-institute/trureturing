# Greedy Residual Allocation

## Abstract

Greedy allocation maximizes one-step gain and positive witnesses force progress.

**Theorem 1.1 (A greedy choice maximizes one-step weighted gain).**

$$[\operatorname{DecidableEq}\left(Definition\right)] \operatorname{IsGreedyChoice}\left(residuals, weight, separates, pool, chosen, definition\right) \Rightarrow \forall alternative \in pool, \operatorname{WeightedGain}\left(residuals, weight, separates, \operatorname{insert}\left(alternative, chosen\right)\right) \leq \operatorname{WeightedGain}\left(residuals, weight, separates, \operatorname{insert}\left(definition, chosen\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidualCoverage/GreedyResidualAllocation.greedy_one_step_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

IsGreedyChoice supplies pool membership and marginal-gain maximality over the finite weighted residual sums.

The insertion identity converts marginal maximality into the stated one-step WeightedGain bound.

**Theorem 1.2 (A positive uncovered witness forces positive greedy progress).**

$$[\operatorname{DecidableEq}\left(Definition\right)] \operatorname{IsGreedyChoice}\left(residuals, weight, separates, pool, chosen, definition\right) \land (\exists alternative \in pool, \exists residual \in residuals, \operatorname{CoveredBy}\left(separates, chosen, residual\right) = false \land \operatorname{separates}\left(alternative, residual\right) = true \land zero < \operatorname{weight}\left(residual\right)) \Rightarrow zero < \operatorname{MarginalGain}\left(residuals, weight, separates, chosen, definition\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidualCoverage/GreedyResidualAllocation.greedy_positive_progress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An available alternative, uncovered residual, true separation, and positive weight form a concrete progress witness.

Greedy maximality transfers its positive marginal gain to the selected definition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ResidualCoverage/GreedyResidualAllocation.greedy_one_step_optimal`
- Truth anchor: `D5/S3/ConceptDynamics/ResidualCoverage/GreedyResidualAllocation.greedy_positive_progress`
- Dependency: [D5/S3/ConceptDynamics/ResidualCoverage/WeightedResidualCoverage](WeightedResidualCoverage.md)
