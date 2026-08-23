# Coordination Best-Response Nonuniqueness

## Abstract

Two coordination equilibria refute unique selection by local best responses.

**Theorem 1.1 (Local best responses do not select a unique social outcome).**

$$\begin{gathered}\forall u: \operatorname{Fin}(2) \to (\operatorname{Fin}(2) \to \{0, 1\}) \to \mathbb{N},\\{}\forall a: \operatorname{Fin}(2) \to \{0, 1\}, \operatorname{Stable}(u, a):= \forall i \in \operatorname{Fin}(2), b \in \{0, 1\}, \operatorname{u}(i, \operatorname{update}(a, i, b)) \leq \operatorname{u}(i, a),\\{}(\forall i \in \operatorname{Fin}(2), a: \operatorname{Fin}(2) \to \{0, 1\}, \operatorname{u}(i, a) = \operatorname{ifEqualThenOneElseZero}(a_{0}, a_{1})) \Rightarrow\\{}\operatorname{Stable}(u, 0^2) \land \operatorname{Stable}(u, 1^2) \land\\{}\neg \exists! a: \operatorname{Fin}(2) \to \{0, 1\}, \operatorname{Stable}(u, a).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/CoordinationBestResponseNonuniqueness.local_best_responses_do_not_select_unique_outcome` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are exactly two players and two Boolean actions. Each player's utility is one when the two actions agree and zero when they differ, exactly as specified by the public payoff hypothesis.

A profile is locally stable when changing either one player's action cannot increase that player's utility. This unilateral comparison is constructed directly in the public statement rather than hidden behind a new equilibrium definition.

At the all-zero profile and at the all-one profile, the current payoff is one and every deviation yields either zero or one. Both profiles therefore consist of best responses. Since the two profiles differ, there cannot be a unique locally stable collective action.

Repository search found a related threshold-public-good theorem, but its utility is different and cannot be reused here. Pinned Mathlib has no exact game-theory theorem for this claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/CoordinationBestResponseNonuniqueness.local_best_responses_do_not_select_unique_outcome`
