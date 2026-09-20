# Least Action and Weighted Greedy Zeckendorf Split Phases

## Abstract

Finite raw split phases stabilize, and greedy split phases maximize full reward.

Indices are zero-based. A split consumes two tokens at its index. Its output is one token at 1 for index 0, tokens at 0 and 2 for index 1, and tokens at i and i+3 for index i+2. SplitPath retains a finite chronological list of legal split indices and all spectator multiplicities. Stable means that every multiplicity is at most one; adjacent occupied sites may remain.

**Theorem 1.1 (Exact site balance).**

$$SplitPath\left(c, d, xs\right) \Rightarrow \forall j, d\left(j\right) + 2 \times count\left(xs, j\right) = c\left(j\right) + incoming\left(xs, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SplitStabilization.split_path_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every legal phase and every site j, final occupancy plus twice the firing count equals initial occupancy plus received tokens. The incoming count is count(xs,1)+count(xs,2) at zero, count(xs,0)+count(xs,3) at one, and count(xs,j-1)+count(xs,j+2) at j at least two.

**Theorem 1.2 (Least action and uniqueness).**

$$SplitPath\left(c, d, xs\right) \land SplitPath\left(c, e, ys\right) \land Stable\left(e\right) \Rightarrow \forall j, count\left(xs, j\right) \le count\left(ys, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SplitStabilization.split_stabilization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal phase fires each site at most as often as any stabilizing phase from the same start. If both phases stabilize, their firing counts and endpoints are equal. At a first attempted excess firing, the balance equation and nonnegative incoming contributions would leave at most one token at the firing site, contradicting legality.

**Theorem 1.3 (Complete split phases exist).**

$$SplitPath\left(start, c, xs\right) \Rightarrow \exists d ys, SplitPath\left(start, d, ys\right) \land Stable\left(d\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SplitStabilization.exists_split_stabilization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given a legal prefix, a finite stabilizing split phase exists from the same start. The recursive construction continues at the prefix endpoint. An enabled split is a carry step, so recursion decreases the existing lexicographic carry measure. The conclusion asserts existence from the same start; it does not expose an extension witness for the supplied prefix.

**Theorem 1.4 (Legal weighted replay across a prefix).**

$$WeightedSplitPath\left(c, d, xs, w\right) \land Enabled\left(c, j\right) \land CrossablePrefix\left(xs, j\right) \Rightarrow PromotedLegalReplay\left(c, d, xs, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SplitStabilization.split_prefix_promotion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If j is enabled and every prefix index differs from j and is below j, the split at j can move before the prefix without decreasing total reward. Index zero can instead cross every other index. Both orders have a common endpoint after firing j and replaying the prefix; replay is legal but need not be greedy. Rewards include the carry and all subsequent sorting switches.

**Theorem 1.5 (Preferred first split in a complete phase).**

$$CompleteWeightedSplitPhase\left(c, d, w\right) \land EnabledZeroOrHighest\left(c, j\right) \Rightarrow PreferredFirstReplay\left(c, d, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SplitStabilization.split_phase_promotion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an enabled split j which is zero or has no duplicate above it. The first-overfire bound forces this split to occur in every stabilizing phase. Extracting its first occurrence gives a legal phase with the same endpoint and no smaller reward, beginning with the chosen split.

**Theorem 1.6 (Greedy split phases maximize reward).**

$$GreedySplitPath\left(c, e, g\right) \land Stable\left(e\right) \land WeightedSplitPath\left(c, d, xs, w\right) \land Stable\left(d\right) \Rightarrow w \le g$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Carry/SplitStabilization.greedy_split_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every raw start and every complete greedy split phase, each complete competing split phase has no greater full reward. Greedy priority selects ones first and otherwise the highest duplicate, recomputed after each split. The proof repeatedly promotes the selected first split and inducts on the greedy continuation. Binary endpoints can still admit merges. No comparison with paths containing merges, or complete ordered-game optimality, follows here.

## References

- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.exists_split_stabilization`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.greedy_split_optimality`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.split_path_balance`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.split_phase_promotion`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.split_prefix_promotion`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.split_stabilization`
