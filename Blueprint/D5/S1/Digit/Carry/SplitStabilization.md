# Least Action for Zeckendorf Split Phases

## Abstract

Finite raw split phases stabilize with unique firing counts and endpoint.

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

Given a legal prefix, a finite stabilizing split phase exists from the same start. The recursive construction continues at the prefix endpoint. An enabled split is a carry step, so recursion decreases the existing lexicographic carry measure. These conclusions compare firing counts, not weighted rewards; ordered longest-game optimality is not established here.

## References

- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.exists_split_stabilization`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.split_path_balance`
- Truth anchor: `D5/S1/Digit/Carry/SplitStabilization.split_stabilization`
