# Dependency-Closure Admission Antitonicity

## Abstract

Expanding a frozen commitment's dependency closure can only remove admissible adjudication evidence.

**Theorem 1.1 (Adjudication admission is antitone in the dependency closure).**

$$\begin{gathered}\forall Evidence, Artifact: \operatorname{Type},\\{}context: \operatorname{AdmissionContext}\left(Evidence, Artifact\right),\\{}oldClosure, newClosure: \operatorname{Set}\left(Artifact\right),\\{}oldClosure \subseteq newClosure \Rightarrow\\{}\forall r: Evidence, \operatorname{AdmissibleJudge}\left(context, newClosure, r\right) \Rightarrow \operatorname{AdmissibleJudge}\left(context, oldClosure, r\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/DependencyClosureAdmissionAntitone.dependency_closure_admission_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The context fixes the event, round, and time prefix of the role ledger, the after-freeze first-seen condition, and provenance reachability. AdmissibleJudge requires an Adjudicate event and rejects both a record that reaches the closure and an adaptive Generate, Tune, or Select event whose dependencies touch it.

If the old closure is contained in the new closure, every old direct reachability witness and every old adaptive-use touch witness is also a witness for the new closure. Negating those two conditions therefore reverses the inclusion at the admission predicate.

This formalizes the dependency-pollution antitonicity clause of Part 48.3 in definition-escape-completion-theory atom generic-residual-661d307df0f3cf908d1089852a0092a99bdea5a95b4148987313a2d4df5e016b. The append-only ledger invariance and set-level contamination clauses remain separate claims.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/DependencyClosureAdmissionAntitone.dependency_closure_admission_antitone`
