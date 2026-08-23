# Finite Split Budget

## Abstract

A finite equivalence partition can split strictly only within its initial class-count deficit.

**Theorem 1.1 (Strict refinements consume the finite class-count budget).**

$$\forall X: \operatorname{Type}, [\operatorname{Fintype}(X)], [\operatorname{DecidableEq}(X)],\ P: \mathbb{N} \to \operatorname{Finpartition}\left(X\right),\ (\forall n\in \mathbb{N}, \operatorname{P}\left(n+1\right) \subseteq \operatorname{P}\left(n\right)) \Rightarrow\\\operatorname{ncard}\left(\{n\in \mathbb{N} \mid \operatorname{P}\left(n+1\right) \neq \operatorname{P}\left(n\right)\}\right) \leq \lvert X \rvert - \operatorname{cardParts}\left(\operatorname{P}\left(0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/FiniteSplitBudget.strict_refinement_count_le_card_sub_initial_classes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be finite and let P_n be equivalence partitions of all of X. The Mathlib finpartition order is the refinement order, so P_(n+1) <= P_n says that each step may split classes but never merge them.

A strict split is exactly an index where the next partition differs. The number of such indices is at most |X| minus the number of parts of P_0, which is the source's initial class count k_0.

The proof directly applies the frozen finite-repair theorem. Pinned Mathlib supplies Finpartition.card_mono, Finpartition.card_parts_le_card, and Set.ncard_Ioc_nat to that underlying argument.

## References

- Truth anchor: `D5/S1/FixedPoints/FiniteSplitBudget.strict_refinement_count_le_card_sub_initial_classes`
- Dependency: [D5/S1/FixedPoints/FiniteRepairTermination](FiniteRepairTermination.md)
