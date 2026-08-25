# Contestability Without Rule Explanation

## Abstract

Exact appeal evidence can make outcomes contestable while the rule remains absent from the explanation log.

**Theorem 1.1 (A contestable outcome need not reveal its governing rule).**

$$\forall T \in \operatorname{Concept}\left(Bool \times Bool, Bool\right),\; \exists R \in \operatorname{Concept}\left(Bool \times Bool, Bool\right), L \in \operatorname{Concept}\left(Bool \times Bool, Unit\right), C \in \operatorname{Concept}\left(Bool \times Bool, Unit\right), A \in \operatorname{Concept}\left(Bool \times Bool, Bool\right),\; A = T \land \left(\operatorname{Refines}\left(\operatorname{canonicalTargetReadout}\left(T\right), \operatorname{conceptJoin}\left(C, A\right)\right) \land \left(\neg \operatorname{Refines}\left(R, L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Appeal/ContestabilityWithoutRuleExplanation.contestable_outcome_can_lack_rule_explanation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean target on a two-coordinate state space, the appeal readout is chosen to equal that target. The joined case-and-appeal interface therefore determines the canonical effective target readout.

Independently, the governing rule reads the second state coordinate while the explanation log is constant. Two states with different rule values have the same log value, so the rule cannot factor through that log.

The public theorem states appeal equality, target contestability, and failed rule explanation as separate clauses on the source readouts.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Appeal/ContestabilityWithoutRuleExplanation.contestable_outcome_can_lack_rule_explanation`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
