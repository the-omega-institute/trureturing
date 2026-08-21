# Finite Repair Termination

## Abstract

Strict refinements of a finite equivalence partition terminate within the available class-count gap, while an infinite carrier admits an infinite refinement tower.

**Theorem 1.1 (Finite repair termination and the infinite boundary).**

$$(\forall X: \operatorname{Type}, [\operatorname{Fintype}(X)], [\operatorname{DecidableEq}(X)],\ P: \mathbb{N} \to \operatorname{Finpartition}\left(X\right),\ (\forall n\in \mathbb{N}, \operatorname{P}\left(n+1\right) \subseteq \operatorname{P}\left(n\right)) \Rightarrow\\(\exists N\in \mathbb{N}, \forall n\in \mathbb{N}, N \leq n \Rightarrow \operatorname{P}\left(n\right) = \operatorname{P}\left(N\right)) \land\\\operatorname{ncard}\left(\{n\in \mathbb{N} \mid \operatorname{P}\left(n+1\right) \neq \operatorname{P}\left(n\right)\}\right) \leq \lvert X \rvert - \operatorname{cardParts}\left(\operatorname{P}\left(0\right)\right)) \land\\(\exists E: \mathbb{N} \to \operatorname{Setoid}\left(\mathbb{N}\right), \forall n\in \mathbb{N}, \operatorname{E}\left(n+1\right) \subset \operatorname{E}\left(n\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/FiniteRepairTermination.finite_repair_termination_and_infinite_tower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite and let P_n be a sequence of partitions of all of X. The order on Mathlib finpartitions is the refinement order, so P_(n+1) <= P_n says that every repair only splits equivalence classes and never merges them.

The sequence is eventually constant. Moreover, the set of indices at which P_(n+1) differs from P_n has cardinality at most |X| minus the number of classes in P_0. This is the claimed sharp budget from the initial concept-class count to the discrete partition.

Pinned Mathlib supplies Finpartition.card_mono, Finpartition.card_parts_le_card, and WellFoundedLT.antitone_chain_condition. The local bookkeeping proves that a proper refinement has strictly more parts and injects strict change indices into the natural-number interval between the initial class count and |X|.

Finiteness is essential: on the natural numbers, the kernel of x |-> min x n has singleton classes below n and one tail class. Increasing n strictly refines this relation forever, giving the source's infinite refinement tower. Inverse-limit construction and audit of a concrete realization are explicitly outside this mathematical declaration and remain implementation obligations.

## References

- Truth anchor: `D5/S1/FixedPoints/FiniteRepairTermination.finite_repair_termination_and_infinite_tower`
