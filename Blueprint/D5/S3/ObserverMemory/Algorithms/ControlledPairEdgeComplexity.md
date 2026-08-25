# Controlled Pair-Edge Complexity

## Abstract

Explicit controlled pair-edge construction has input-linear quadratic resource bounds.

**Theorem 1.1 (Explicit controlled pair edges have quadratic state complexity).**

$$\begin{gathered}\forall U, Y,\\{}\operatorname{Finite}(U), \operatorname{Finite}(Y),\\{}F: U \to Y \to Y,\\{}(\operatorname{controlledTimeBudget}(F) \leq 2 \times \operatorname{card}(U) \times \operatorname{card}(Y)^{2}) \land\\{}(\operatorname{controlledSpaceBudget}(F) \leq 3 \times \operatorname{card}(U) \times \operatorname{card}(Y)^{2}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ControlledPairEdgeComplexity.controlled_pair_edge_complexity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the input and state carriers be finite, and let each input select a deterministic state-update channel. For one channel, the canonical explicit reverse table contains the reversed edge of every ordered state pair.

Controlled time and storage are constructed by summing the repository's per-channel reverse-search budgets over all inputs. Thus time is at most twice, and storage at most three times, the input count times the square of the state count.

The proof directly applies reverse_bfs_correct_and_quadratic to each controlled channel and sums its two resource inequalities. Repository and pinned-library searches found no theorem already packaging both controlled full-table bounds.

This formalizes the two boxed resource clauses of theorem 25.6. The subsequent online-enumeration sentence is qualitative and depends on implementation-specific structure, so it is not asserted as a universal mathematical clause.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlledPairEdgeComplexity.controlled_pair_edge_complexity`
- Dependency: [D5/S3/Observer/DynamicProgramming/ReverseBfsDistance](../../Observer/DynamicProgramming/ReverseBfsDistance.md)
