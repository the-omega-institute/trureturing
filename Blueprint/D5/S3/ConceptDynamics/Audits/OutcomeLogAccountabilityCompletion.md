# Outcome Log Accountability Completion

## Abstract

Outcome-only logs omit accountability, whose canonical completion is least.

**Theorem 1.1 (Outcome-only logs cannot recover full accountability).**

$$\begin{gathered}\forall Z, Decision, Rule, Actor, Provenance: \operatorname{Type},\\{}D: Z \to Decision, R: Z \to Rule,\\{}A: Z \to Actor, P: Z \to Provenance,\\{}z, zp: Z,\\{}D\left(z\right) = D\left(zp\right) \land (A\left(z\right) \neq A\left(zp\right) \lor R\left(z\right) \neq R\left(zp\right)) \Rightarrow\\{}(\forall Log: \operatorname{Type}, L: Z \to Log,\\{}\operatorname{Refines}\left(L, D\right) \Rightarrow \neg \operatorname{Refines}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(D, R\right), A\right), P\right), L\right)) \land\\{}\forall Log: \operatorname{Type}, L: Z \to Log,\\{}\operatorname{Refines}\left(L, \operatorname{conceptJoin}\left(L, \operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(D, R\right), A\right), P\right)\right)\right) \land\\{}\operatorname{Refines}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(D, R\right), A\right), P\right), \operatorname{conceptJoin}\left(L, \operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(D, R\right), A\right), P\right)\right)\right) \land\\{}\forall Candidate: \operatorname{Type}, K: Z \to Candidate,\\{}(\operatorname{Refines}\left(L, K\right) \land \operatorname{Refines}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(D, R\right), A\right), P\right), K\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(L, \operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(\operatorname{conceptJoin}\left(D, R\right), A\right), P\right)\right), K\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/OutcomeLogAccountabilityCompletion.outcome_log_obstruction_and_accountability_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Decision, rule, actor, and provenance are independent readouts on the same state carrier. Their nested canonical join is the full accountability readout.

A log that factors through the decision identifies the displayed witness states. Their different actor or rule coordinate makes the full accountability readout vary on that log fiber, so no recovery factor can exist.

Joining the log with the accountability readout retains each component. Pairing any two supplied factors proves that this completion is below every common refinement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/OutcomeLogAccountabilityCompletion.outcome_log_obstruction_and_accountability_completion`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](../NormativeStructure/HistorySensitiveOutcomeReductionObstruction.md)
