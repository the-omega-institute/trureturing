# Label transport across closed matching intervals

## Abstract

Label transport across closed matching intervals.

**Theorem 1.1 (Label transport across closed matching intervals).**

$$\forall L \in \mathit{Type},\; \forall n \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(n\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(n + 1\right), L\right),\; \forall l \in \operatorname{Fin}\left(n + 1\right),\; \forall r \in \operatorname{Fin}\left(n + 1\right),\; \operatorname{Compatible}\left(M, y\right) \Rightarrow \left(l \le r \Rightarrow \left(\operatorname{IntervalClosed}\left(M, l, r\right) \Rightarrow \operatorname{Apply}\left(y, l\right) = \operatorname{Apply}\left(y, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals.closed_interval_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A partner-closed interval has equal boundary labels under every compatible labelling. Strong induction removes its first matched block and retains a closed suffix. The interval may contain any number of nested or disjoint arcs, and zero length is included.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals.closed_interval_gap`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingCore](OrderedMatchingCore.md)
