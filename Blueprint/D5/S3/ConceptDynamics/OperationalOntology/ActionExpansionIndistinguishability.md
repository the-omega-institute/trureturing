# Action Expansion and Indistinguishability

## Abstract

More allowed actions can only remove behavioral identifications.

**Definition 1.1 (Behavioral indistinguishability under allowed actions).**

$$x \sim_{M} y \Leftrightarrow \forall m\in M, O(F_{m}(x)) = O(F_{m}(y)).$$

*Formalization.* `D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability.actionIndistinguishability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two states are behaviorally indistinguishable for an allowed action set when every action in that set produces equal public readouts.

**Theorem 1.2 (Action expansion shrinks indistinguishability).**

$$\begin{gathered}\forall A, X, B: \operatorname{Type}, M, M_{\mathrm{expanded}}\subset A, F: A \to X \to X, O: X \to B,\\{}M\subseteq M_{\mathrm{expanded}} \Rightarrow\\{}\sim_{M_{\mathrm{expanded}}}\subseteq \sim_{M}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability.action_expansion_shrinks_indistinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The action map and public readout are independent source primitives. The two relations use the same state, action, and output carriers.

If the original allowed actions are contained in the expanded set, every pair agreeing after all expanded actions also agrees after each original action.

Pinned Mathlib supplies the exact bounded-intersection inclusion lemma; the Lean theorem is a thin application to the equal-output relations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability.actionIndistinguishability`
- Truth anchor: `D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability.action_expansion_shrinks_indistinguishability`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
