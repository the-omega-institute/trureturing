# Finite Discussion Stability

## Abstract

A finite discussion admits at most the initially unresolved number of strict refinements.

**Theorem 1.1 (Finite discussions have a sharp strict-refinement budget).**

$$\begin{gathered}\forall X: \operatorname{Type}^{*}, [\operatorname{Fintype}(X)], steps: \mathbb{N},\\{}Coordinate: \operatorname{Fin}(steps+1) \to \operatorname{Type}^{*},\\{}concept: (i: \operatorname{Fin}(steps+1)) \to \operatorname{Concept}(X, \operatorname{Coordinate}(i)),\\{}(\forall i: \operatorname{Fin}(steps+1), \operatorname{Surjective}(\operatorname{concept}(i))),\\{}(\forall i: \operatorname{Fin}(steps), \operatorname{StrictRefinement}(\operatorname{concept}(i.castSucc), \operatorname{concept}(i.succ))),\\{}steps \leq \lvert X \rvert - \lvert \operatorname{range}(\operatorname{concept}(0)) \rvert.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Discussion/FiniteDiscussionStability.finite_discussion_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a finite state space and let q_i : X -> C_i be the concept readout after i strict information-growth steps. Each readout is surjective, so its coordinate type records exactly its attained concept classes rather than unused labels.

Every nonredundant message is represented by the repository's canonical StrictRefinement relation from q_i to q_(i+1). A refinement factor is surjective on effective coordinate types. If their finite cardinalities were equal, Mathlib's finite surjection criterion would make the factor bijective and its inverse would give the forbidden reverse refinement.

Consequently every message increases the number of attained concept classes by at least one. The final class count is at most |X|, while surjectivity identifies the initial coordinate count with |Im(q_0)|. Therefore n <= |X| - |Im(q_0)|, exactly the finite discussion bound.

Repository search supplied ConceptJoinUniversal.Refines and StrictRefinementCapability.StrictRefinement. Pinned Mathlib supplied Nat.bijective_iff_surjective_and_card, Nat.card_le_card_of_surjective, and Nat.card_congr; no existing declaration packages the arbitrary-discussion bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Discussion/FiniteDiscussionStability.finite_discussion_stability`
- Dependency: [D5/S3/ConceptDynamics/StrictRefinementCapability](../StrictRefinementCapability.md)
