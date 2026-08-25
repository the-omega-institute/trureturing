# Outcome Correctness Without Procedure Auditability

## Abstract

An exact target judgment can coexist with a procedure certificate that the audit log cannot recover.

**Theorem 1.1 (A correct outcome need not be procedurally auditable).**

$$\forall T \in \operatorname{Concept}\left(Bool, Bool\right),\; \exists R \in \operatorname{Concept}\left(Bool, Unit\right), A \in \operatorname{Concept}\left(Bool, Bool\right), H \in \operatorname{Concept}\left(Bool, Unit\right), P \in \operatorname{Concept}\left(Bool, Unit\right), J \in \operatorname{Concept}\left(Bool, Bool\right), L \in \operatorname{Concept}\left(Bool, Unit\right),\; J = T \land \left(\neg \operatorname{Refines}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(R, A\right), H\right), P\right), L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/OutcomeCorrectnessWithoutProcedureAudit.correct_outcome_can_lack_procedure_auditability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary Boolean target, the exhibited judgment returns that target exactly. Thus factual correctness is held fixed rather than inferred from the procedure channels.

The authorization channel distinguishes the two Boolean cases, while rules, hearing, provenance, and the audit log are constant. The canonical nested concept join therefore distinguishes cases that the log merges, so its procedure certificate cannot factor through the log.

The public statement exposes the four source channels, their canonical join, the judgment-target equality, and the failed refinement directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/OutcomeCorrectnessWithoutProcedureAudit.correct_outcome_can_lack_procedure_auditability`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
