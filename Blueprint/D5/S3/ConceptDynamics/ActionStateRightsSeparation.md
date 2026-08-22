# Negative and Positive Rights

## Abstract

Empty action states separate non-infringement from positive realization.

**Theorem 1.1 (No available action separates the two rights).**

$$\forall State, Action: \operatorname{Type}, x: State, U_{x}, V_{x}: \operatorname{Set} Action, F: Action \to State \to State, G: \operatorname{Set} State,\ V_{x} \subseteq U_{x} \Rightarrow\ U_{x} = \emptyset \Rightarrow\ \neg {x \in G} \Rightarrow\ {\forall N: \operatorname{Set} Action, N \subseteq U_{x} \Rightarrow \operatorname{negativeRight}(N, V_{x})} \land \neg \operatorname{positiveRight}(U_{x}, F, G, x) \land \neg {x \in G \lor \operatorname{positiveRight}(U_{x}, F, G, x)} \land \neg {{\forall N: \operatorname{Set} Action, N \subseteq U_{x} \Rightarrow \operatorname{negativeRight}(N, V_{x})} \iff \operatorname{positiveRight}(U_{x}, F, G, x)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ActionStateRightsSeparation.no_action_state_separates_rights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An allowed-action set, a chosen-action set, a transition, and a goal set are the source primitives. A negative right is disjointness from the chosen actions; a positive right requires an allowed transition into the goal.

When the allowed-action set is empty and chosen actions are restricted to it, every forbidden subset is harmless, while the positive goal and its realization condition both fail outside the goal.

The four public conjuncts expose the negative-right clause, positive failure, realization failure, and non-equivalence of the predicates.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ActionStateRightsSeparation.no_action_state_separates_rights`
