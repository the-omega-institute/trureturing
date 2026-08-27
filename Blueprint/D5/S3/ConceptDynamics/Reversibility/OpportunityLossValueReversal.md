# Opportunity Loss Can Reverse Waiting Value

## Abstract

Losing an available action while waiting can strictly lower optimal value.

**Theorem 1.1 (Opportunity loss can reverse waiting value).**

$$\begin{gathered}\exists \mathbb{E}: \operatorname{Concept}\left(Unit \to \mathbb{R}, \mathbb{R}\right), q: \operatorname{Concept}\left(Unit, Unit\right),\\{}T: Unit \to Unit \to Unit, V: \operatorname{Concept}\left(Unit, Bool \to \mathbb{R}\right),\\{}A: \operatorname{Set}\left(Bool\right), B: Unit \to \operatorname{Set}\left(Bool\right),\\{}\pi: \operatorname{Set}\left(Unit \to Bool\right), W, Z: \mathbb{R},\\{}(\forall e: Unit, x: Unit, T(e)(x) = x) \land\\{}(\forall u: Bool, u \in A \Rightarrow \operatorname{const}\left(u\right) \in \pi) \land\\{}(\exists e: Unit, u: Bool, u \in A \land \neg(u \in B(e))) \land\\{}\operatorname{IsGreatest}\left(\{\operatorname{uninformedExpectedValue}\left(\mathbb{E}, V, u\right) \mid u \in A\}, W\right) \land\\{}\operatorname{IsGreatest}\left(\{\operatorname{informedExpectedValue}\left(\mathbb{E}, q, T, V, 0, p\right) \mid p \in \operatorname{admissiblePolicies}\left(\pi, B\right)\}, Z\right) \land\\{}Z < W.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/OpportunityLossValueReversal.opportunity_loss_can_reverse_waiting_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness uses one state, one observation, and two actions. The world does not change, information has zero cost, and every constant policy is available as a candidate.

Before waiting both actions are available. After observation only the lower-utility action remains, so the opportunity-loss witness and both optimization claims refer to the same action sets and utility.

The best immediate action has value one, whereas every admissible waiting policy must select the remaining action and has value zero. Thus the optimal waiting value is strictly lower.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/OpportunityLossValueReversal.opportunity_loss_can_reverse_waiting_value`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue](../DecisionValue/FreeInformationValue.md)
