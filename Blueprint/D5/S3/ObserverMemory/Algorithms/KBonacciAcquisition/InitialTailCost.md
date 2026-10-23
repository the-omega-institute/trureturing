# Initial tail acquisition and sharp block cost

## Abstract

Exact initial-tail budgets on all actual complete-block histories.

**Theorem 1.1 (Every feasible budget for the complete initial tail).**

$$\forall k \in \mathbb{N},\; \forall m \in \mathbb{N},\; \left(2 \le k \land 1 \le m\right) \Rightarrow \left(\forall alphabet \in Bool,\; \forall n \in \mathbb{N},\; \left(\exists controller \in \operatorname{Option}\left(\operatorname{ZMod}\left(2\right)\right) \to \operatorname{AcquisitionTree}\left(k, m, alphabet, \operatorname{Option}\left(\mathbb{N}\right), n\right),\; \forall history \in \operatorname{List}\left(\operatorname{AllowedBlock}\left(k, m, alphabet\right)\right),\; \operatorname{result}\left(controller\left(\operatorname{endpointReading}\left(\operatorname{historyRecord}\left(history\right)\right)\right), \operatorname{historyRecord}\left(history\right)\right) = \operatorname{map}\left(\operatorname{tail}, \operatorname{historyRecord}\left(history\right)\right)\right) \Leftrightarrow \left(\left(m = 1 \land k - 1 \le n\right) \lor \left(k = 2 \land 1 \le n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InitialTailCost.initial_tail_budget_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original order k>=2 and width m>=1, alphabet=false allows every binary block, while alphabet=true allows blocks with no internal run of k ones. Each history is any finite sequence in the selected alphabet, including the empty history and histories that have rejected. historyRecord is generated from the empty word by literal chronological bit updates, using the original KBonacci weights and fixed mod-two reading. The target is its initial tail: some(s) for a live initial record and none for an initially rejected record.

The controller receives the initial endpoint output for free. Its finite tree has uniform horizon n; each step issues exactly one full block and follows the attained endpoint reply. No internal bit output, reset, copy, initial phase clock or unexecuted branch is provided. The label refers to the initial history even when an issued block changes or rejects it. Actual joint realization supplies every live value-phase-tail record in SourceRecord and the absorbing rejected record.

Thus the full initial tail is acquired exactly when m=1 or k=2. For m=1 the least worst-case number of additional blocks is k-1. Sequential ones label a first rejection at step r by initial tail k-r; after k-1 successes the initial tail is zero. Same-value, same-phase adjacent tails zero and one have the same outputs before step k-1, and any earlier zero merges their records. Induction over arbitrary adaptive trees yields the lower bound.

For k=2 and every positive width, a leading one followed by zeros rejects initial tail one and preserves initial tail zero, so the least worst-case cost is one block. A zero-block tree cannot distinguish the two same-value actual tails. For k>=3 and m>=2, the first-zero criterion rules out the full tail target: clearing merges at least two survivors or rejection merges at least two distinct tails. The all-one branch also merges at least two rejected tails. Initial rejection stops freely with its separate none label. The overlap m=1,k=2 gives the same one-block cost.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InitialTailCost.initial_tail_budget_exact`
- Dependency: [D5/S3/ObserverMemory/Algorithms/KBonacciIrreversibleAcquisition](../KBonacciIrreversibleAcquisition.md)
