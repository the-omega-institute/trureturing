# Voluntariness Action-Factorization Obstruction

## Abstract

Equal actions with different voluntariness status obstruct action-only evaluation.

**Theorem 1.1 (An action result does not identify voluntariness).**

$$\begin{gathered}\forall Gamma, Action, AuthorizationStatus: \operatorname{Type},\\{}A: Gamma \to Action, V: Gamma \to AuthorizationStatus,\\{}gamma, gammaPrime: Gamma,\\{}A(gamma) = A(gammaPrime) \land V(gamma) \neq V(gammaPrime) \Rightarrow\\{}\neg (\exists v: Action \to AuthorizationStatus, V = \operatorname{compose}(v, A)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/NormativeStructure/VoluntarinessActionFactorizationObstruction.action_result_does_not_identify_voluntariness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The path carrier, action readout, and normative voluntariness evaluation are independent public source primitives on the canonical concept carrier. The freely chosen and coerced paths are also public.

The hypotheses state that the two paths have one action result but different authorization status. The conclusion directly denies any function of the action result through which the full voluntariness evaluation factors.

Repository search found the exact frozen family theorem for equal endpoints with different normative evaluations. The Lean proof packages the two named paths as its witness and applies that theorem directly, with no local reproof or duplicate provenance primitive.

A constant Unit-valued action and identity Boolean evaluation compile as a concrete inhabited model of the hypotheses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/NormativeStructure/VoluntarinessActionFactorizationObstruction.action_result_does_not_identify_voluntariness`
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](HistorySensitiveOutcomeReductionObstruction.md)
