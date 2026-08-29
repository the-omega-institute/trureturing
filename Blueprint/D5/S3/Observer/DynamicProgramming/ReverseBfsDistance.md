# Reverse Search for First Separation

## Abstract

Reverse breadth-first search computes first-separation depths in quadratic resources.

**Theorem 1.1 (Reverse breadth-first search is correct and quadratic).**

$$\begin{gathered}\forall Y, O, [\operatorname{Fintype}(Y)], [\operatorname{DecidableEq}(Y)], [\operatorname{DecidableEq}(O)],\\{}\tau: Y \to Y, q: Y \to O,\\{}\operatorname{reverseBfsDistance}(\tau, q) = \operatorname{exactSeparationDepth}(\tau, q) \land\\{}\operatorname{reverseBfsTimeBudget}(\tau) \leq 2 \lvert Y\rvert^{2} \land\\{}\operatorname{reverseBfsSpaceBudget}(\tau) \leq 3 \lvert Y\rvert^{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/ReverseBfsDistance.reverse_bfs_correct_and_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite deterministic state space with update tau and readout q. The pair successor sends each ordered pair to the pair of its updated states, and the initial search table contains exactly the pairs with unequal current readouts.

The reverse search expands cumulatively from all initial mismatches. Its output is the first visit depth, with no value for a pair that is never visited. The semantic comparison depth is independently constructed as the first future readout mismatch, again with no value for infinity.

The time budget counts one queue visit per ordered pair and one scan per stored reversed edge. The space budget counts that explicit edge table, one distance slot per pair, and a queue with one slot per pair. These constructed budgets are bounded by two and three times the square of the state count, respectively.

Correctness follows by identifying the depth-k visited table with pairs having a mismatch witness of length at most k, then comparing the two least witnesses. The explicit reversed edge table has one edge for every ordered state pair.

## References

- Truth anchor: `D5/S3/Observer/DynamicProgramming/ReverseBfsDistance.reverse_bfs_correct_and_quadratic`
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../Separation/FiniteFutureCongruence.md)
