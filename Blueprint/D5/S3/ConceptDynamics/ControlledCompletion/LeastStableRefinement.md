# Least Stable Controlled Completion

## Abstract

Action-word completion is the least interface stable under every generating action.

**Theorem 1.1 (Controlled completion is the least stable refinement).**

$$\forall X \in \operatorname{Type}, A \in \operatorname{Type}, U \in \operatorname{Type}, q \in X \to A, intervene \in U \to \left(X \to X\right),\; \operatorname{Refines}\left(q, \operatorname{DynClosure}\left(q, intervene\right)\right) \land \left(\operatorname{InterventionClosed}\left(\operatorname{DynClosure}\left(q, intervene\right), intervene\right) \land \left(\forall B \in \operatorname{Type}, candidate \in X \to B,\; \left(\operatorname{Refines}\left(q, candidate\right) \land \operatorname{InterventionClosed}\left(candidate, intervene\right)\right) \Rightarrow \operatorname{Refines}\left(\operatorname{DynClosure}\left(q, intervene\right), candidate\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ControlledCompletion/LeastStableRefinement.controlled_completion_is_least_stable_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an interface q and a family of generating actions, the canonical dynamic closure records q after every finite action word.

Its empty-word coordinate recovers q, prefixing a generator preserves all closure fibers, and every other action-stable refinement determines every finite-word coordinate. These are the three public clauses of the least-interface claim.

The theorem imports the existing dynamic-closure construction and applies its three frozen component theorems directly. Repository and pinned-Mathlib searches found no theorem already bundling the clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ControlledCompletion/LeastStableRefinement.controlled_completion_is_least_stable_refinement`
- Dependency: [D5/S3/ConceptDynamics/Interventions/DynamicClosureMinimality](../Interventions/DynamicClosureMinimality.md)
