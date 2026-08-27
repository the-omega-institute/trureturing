# World Change Can Reverse Waiting Value

## Abstract

A changed world can make waiting strictly worse despite preserving every action.

**Theorem 1.1 (World change can reverse waiting value).**

$$\begin{gathered}\exists \mathbb{E}: \operatorname{Concept}\left(Bool \to \mathbb{R}, \mathbb{R}\right), q: \operatorname{Concept}\left(Bool, Unit\right),\\{}T: Unit \to Bool \to Bool, V: \operatorname{Concept}\left(Bool, Unit \to \mathbb{R}\right),\\{}A: \operatorname{Set}\left(Unit\right), B: Unit \to \operatorname{Set}\left(Unit\right),\\{}\pi: \operatorname{Set}\left(Unit \to Unit\right), W, Z: \mathbb{R},\\{}(\exists e: Unit, x: Bool, T(e)(x) \neq x) \land\\{}(\forall u: Unit, u \in A \Rightarrow \operatorname{const}\left(u\right) \in \pi) \land\\{}(\forall e: Unit, A \subseteq B(e)) \land\\{}\operatorname{IsGreatest}\left(\{\operatorname{uninformedExpectedValue}\left(\mathbb{E}, V, u\right) \mid u \in A\}, W\right) \land\\{}\operatorname{IsGreatest}\left(\{\operatorname{informedExpectedValue}\left(\mathbb{E}, q, T, V, 0, p\right) \mid p \in \operatorname{admissiblePolicies}\left(\pi, B\right)\}, Z\right) \land\\{}Z < W.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/WorldChangeValueReversal.world_change_can_reverse_waiting_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness has two world states, one observation, and one action. Waiting changes the initially evaluated state, while information has zero cost and the action set is preserved exactly.

Every constant policy is available. The same transition that witnesses world change is used by the informed-value functional, so the positive safeguards and strict reversal are not separable constructions.

Immediate action has value one at the initial state. After waiting, the world transition reaches the zero-utility state, so every admissible policy has value zero and waiting is strictly worse.

The theorem reuses the canonical decision-value primitives. The adjacent opportunity-loss theorem changes the action set instead of the world, and repository and pinned-library searches found no exact theorem for this countermodel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/WorldChangeValueReversal.world_change_can_reverse_waiting_value`
- Dependency: [D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue](../DecisionValue/FreeInformationValue.md)
