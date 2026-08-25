# Residual Separation Adapter

## Abstract

Finite defect snapshots are covered exactly when no chosen-package pair stays blind.

**Theorem 1.1 (Exact cover is equivalent to absence of blind residual pairs).**

$$[\operatorname{DecidableEq}\left(Output\right)] [\operatorname{DecidableEq}\left(\operatorname{Concept}\left(X, Output\right)\right)] \forall pair \in residuals, pair \in \operatorname{defectRelation}\left(q, target\right) \Rightarrow (\operatorname{ExactCover}\left(residuals, separatesPair, chosen\right) \iff \forall pair \in residuals, \neg \operatorname{InBlindResidual}\left(pair, chosen, q, target\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter.exactCover_iff_no_blind_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The snapshot lists defectRelation pairs; Boolean separation by the chosen package is translated through the canonical joint kernel.

The coveredBy bridge gives the exact-cover biconditional pair by pair.

**Theorem 1.2 (Positive residual weights make zero uncovered weight equivalent to no blind pair).**

$$[\operatorname{DecidableEq}\left(Output\right)] [\operatorname{DecidableEq}\left(\operatorname{Concept}\left(X, Output\right)\right)] \forall pair \in residuals, pair \in \operatorname{defectRelation}\left(q, target\right) \land \forall pair \in residuals, zero < \operatorname{weight}\left(pair\right) \Rightarrow (\operatorname{UncoveredWeight}\left(residuals, weight, separatesPair, chosen\right) = zero \iff \forall pair \in residuals, \neg \operatorname{InBlindResidual}\left(pair, chosen, q, target\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter.uncoveredWeight_zero_iff_no_blind_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same defect snapshot is assigned a strictly positive natural weight at every residual pair.

Consequently, uncoveredWeight is zero exactly when every snapshot pair is covered, hence exactly when no chosen-package pair remains blind.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter.exactCover_iff_no_blind_pair`
- Truth anchor: `D5/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter.uncoveredWeight_zero_iff_no_blind_pair`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](../DefinitionEscape/BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/ResidualCoverage/WeightedResidualCoverage](WeightedResidualCoverage.md)
