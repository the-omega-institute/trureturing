# Weighted Residual Coverage

## Abstract

Finite weighted residual capture is monotone submodular with cover boundaries.

**Theorem 1.1 (Weighted gain has diminishing returns).**

$$[\operatorname{DecidableEq}\left(Definition\right)] \operatorname{Subset}\left(smaller, larger\right) \Rightarrow\operatorname{WeightedGain}\left(residuals, weight, separates, \operatorname{insert}\left(definition, larger\right)\right) + \operatorname{WeightedGain}\left(residuals, weight, separates, smaller\right) \leq \operatorname{WeightedGain}\left(residuals, weight, separates, \operatorname{insert}\left(definition, smaller\right)\right) + \operatorname{WeightedGain}\left(residuals, weight, separates, larger\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidualCoverage/WeightedResidualCoverage.weightedGain_submodular_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

WeightedGain and MarginalGain are finite sums over the fixed residual universe with its weight and separation predicate.

The insertion identity reduces the four-term inequality to marginalGain_antitone, so larger selected sets have no larger additional gain.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ResidualCoverage/WeightedResidualCoverage.weightedGain_submodular_insert`
