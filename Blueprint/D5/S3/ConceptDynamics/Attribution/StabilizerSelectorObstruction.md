# Stabilizer Obstruction to Equivariant Selection

## Abstract

A stabilizer without an admissible fixed action obstructs every equivariant selector.

**Theorem 1.1 (No equivariant selector exists without a stabilizer-fixed action).**

$$\begin{gathered}\forall G, X, A: \operatorname{Type},\\{}[\operatorname{Group}\left(G\right)], [\operatorname{MulAction}\left(G, X\right)], [\operatorname{MulAction}\left(G, A\right)],\\{}admissible: X \to \operatorname{Set}\left(A\right), x: X,\\{}(\forall a: A, a \in admissible\left(x\right) \Rightarrow \exists g: G, \operatorname{smul}\left(g, x\right) = x \land \operatorname{smul}\left(g, a\right) \neq a) \Rightarrow \neg \exists s: X \to A,\\{}(\forall y: X, s\left(y\right) \in admissible\left(y\right)) \land (\forall g: G, y: X, s\left(\operatorname{smul}\left(g, y\right)\right) = \operatorname{smul}\left(g, s\left(y\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction.no_equivariant_selector_of_stabilizer_without_fixed_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a group act on both states and actions. At the named state, every admissible action is moved by some group element that fixes the state; this states directly that the stabilizer has no admissible fixed action.

An admissible deterministic selector would choose one of those actions. Equivariance under the corresponding stabilizer element would both fix and move the selected action, a contradiction.

The existing finite-permutation culprit theorem is only a specialization. Repository and pinned-Mathlib searches found no general group-action theorem with the public admissible-set and stabilizer clauses.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction.no_equivariant_selector_of_stabilizer_without_fixed_action`
