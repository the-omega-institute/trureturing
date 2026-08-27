# Action Expansion Indistinguishability Law

## Abstract

A separating new action can make behavioral indistinguishability shrink strictly.

**Theorem 1.1 (Action expansion reveals previously hidden distinctions).**

$$\begin{gathered}\forall A, X, B: \operatorname{Type},\\{}M, M_{expanded}: \operatorname{Set}\left(A\right), F: A \to X \to X, O: X \to B,\\{}M \subseteq M_{expanded} \Rightarrow\\{}{\sim_{M_{expanded}} \subseteq \sim_{M}} \land\\{}{\forall u\in {M_{expanded} \setminus M}, \forall x, y: X, x \sim_{M} y \land O(F(u)(x)) \neq O(F(u)(y)) \Rightarrow \neg{x \sim_{M_{expanded}} y}} \land\\{}{\exists M_{0}, M_{1}: \operatorname{Set}\left(Unit\right), F_{0}: Unit \to Bool \to Bool, O_{0}: Bool \to Bool, x_{0}, y_{0}: Bool, M_{0} \subset M_{1} \land x_{0} \sim_{M_{0}} y_{0} \land \neg{x_{0} \sim_{M_{1}} y_{0}}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishabilityLaw.action_expansion_indistinguishability_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary action, state, and output carriers, agreement under every expanded action implies agreement under every original action.

If a newly available action gives unequal public outputs on a pair from the original indistinguishability relation, that pair is absent from the expanded relation.

The public countermodel uses empty and singleton Unit action sets with the identity Boolean transition. The same states belong to the original relation and fail to belong to the expanded relation, so the converse inclusion is not valid in general.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishabilityLaw.action_expansion_indistinguishability_law`
- Dependency: [D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability](ActionExpansionIndistinguishability.md)
