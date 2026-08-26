# Procedure-Derived Correct Outcome

## Abstract

A judgment computed from a four-channel procedure certificate can match its target even when the audit log cannot recover that certificate.

**Theorem 1.1 (Correct output does not imply procedure auditability).**

$$\forall T \in \operatorname{Concept}\left(Bool, Bool\right),\; \exists R \in \operatorname{Concept}\left(Bool, Unit\right), A \in \operatorname{Concept}\left(Bool, \operatorname{TargetImage}\left(identityBool\right)\right), H \in \operatorname{Concept}\left(Bool, Unit\right), P \in \operatorname{Concept}\left(Bool, Unit\right), L \in \operatorname{Concept}\left(Bool, Unit\right), oracle \in (((Unit \times \operatorname{TargetImage}\left(identityBool\right)) \times Unit) \times Unit) \to Bool,\; oracle \circ \operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(R, A\right), H\right), P\right) = T \land \left(\neg \operatorname{Refines}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(R, A\right), H\right), P\right), L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/ProcedureDerivedCorrectOutcome.procedure_derived_correct_outcome_can_lack_auditability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rules, authorization, hearing, and provenance readouts form the canonical nested procedure certificate. The displayed judgment is the oracle composed with that certificate, so it is not an independent witness chosen equal to the target.

The construction uses an authorization readout that retains the Boolean case. It therefore supports exact target recovery while making the same certificate distinguish two cases merged by the constant log.

Thus the positive equality and the failed refinement are consequences of one shared procedure construction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/ProcedureDerivedCorrectOutcome.procedure_derived_correct_outcome_can_lack_auditability`
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
