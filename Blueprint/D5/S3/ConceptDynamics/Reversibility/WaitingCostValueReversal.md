# Waiting Cost Can Reverse Value

## Abstract

Positive waiting cost alone can make delayed optimal value strictly lower.

**Theorem 1.1 (Positive waiting cost can reverse optimal value).**

$$\begin{gathered}\exists \mathbb{E}: \operatorname{Concept}\left(Unit \to \mathbb{R}, \mathbb{R}\right), q: \operatorname{Concept}\left(Unit, Unit\right),\\{}T: Unit \to Unit \to Unit, V: \operatorname{Concept}\left(Unit, Unit \to \mathbb{R}\right),\\{}A: \operatorname{Set}\left(Unit\right), B: Unit \to \operatorname{Set}\left(Unit\right),\\{}\pi: \operatorname{Set}\left(Unit \to Unit\right),\\{}c: \mathbb{R}, W, Z: \mathbb{R},\\{}0 < c \land\\{}(\forall e: Unit, x: Unit, T(e)(x) = x) \land\\{}(\forall u: Unit, u \in A \Rightarrow \operatorname{const}\left(u\right) \in \pi) \land\\{}(\forall e: Unit, B(e) = A) \land\\{}\operatorname{IsGreatest}\left(\{\operatorname{uninformedExpectedValue}\left(\mathbb{E}, V, u\right) \mid u \in A\}, W\right) \land\\{}\operatorname{IsGreatest}\left(\{\operatorname{informedExpectedValue}\left(\mathbb{E}, q, T, V, c, p\right) \mid p \in \operatorname{admissiblePolicies}\left(\pi, B\right)\}, Z\right) \land\\{}Z < W.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/WaitingCostValueReversal.positive_waiting_cost_can_reverse_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness has one state, one observation, and one action. Observation leaves the world unchanged, the action set is exactly preserved, and the constant policy remains admissible.

Immediate action has value one. Delayed action has the same gross utility and a positive cost of one, so its net value is zero.

Both optimality claims and the strict comparison use this same decision model; positive cost is the only failed safeguard.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/WaitingCostValueReversal.positive_waiting_cost_can_reverse_value`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue](../DecisionValue/FreeInformationValue.md)
