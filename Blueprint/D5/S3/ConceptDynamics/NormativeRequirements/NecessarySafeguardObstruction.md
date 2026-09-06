# Necessary Safeguard Obstruction

## Abstract

Necessary requirements constrain permission even when a stated goal or outcome agrees.

**Theorem 1.1 (A violated necessary requirement excludes permission).**

Lean statement: `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.violated_requirement_excludes_permission`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.violated_requirement_excludes_permission` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Permission and the indexed requirements are independent Concept predicates. The premise says every permitted path satisfies every requirement. A witness to a violated requirement therefore excludes that path. This theorem does not select or justify the necessity rule.

**Theorem 1.2 (Achieving a goal need not suffice for permission).**

Lean statement: `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.rationale_does_not_supply_necessary_safeguard`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.rationale_does_not_supply_necessary_safeguard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a goal-achieving path that violates a necessary safeguard, that path is excluded and witnesses failure of the universal goal-to-permission rule. Goal achievement is not defined to include permission or the safeguard.

**Theorem 1.3 (Equal outcomes with different permissions obstruct outcome-only decisions).**

Lean statement: `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.necessary_safeguard_blocks_readout_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.necessary_safeguard_blocks_readout_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two paths have equal outcome readouts. One is permitted; the other violates a necessary safeguard. Their distinct permission values are derived, then the existing history-sensitive outcome factorization theorem is applied. A natural-number capacity and parity example supplies inhabited premises. Consent, rights, safety, and authorization can instantiate the predicates, but real-world facts and the authority of a normative standard are not proved.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.necessary_safeguard_blocks_readout_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.rationale_does_not_supply_necessary_safeguard`
- Truth anchor: `D5/S3/ConceptDynamics/NormativeRequirements/NecessarySafeguardObstruction.violated_requirement_excludes_permission`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](../NormativeStructure/HistorySensitiveOutcomeReductionObstruction.md)
