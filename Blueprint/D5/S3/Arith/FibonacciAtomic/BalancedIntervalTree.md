# Balanced Interval Trees

## Abstract

Ordered interval bisection controls all node blocks and attains logarithmic height.

Coordinates are numbered from zero through k. For natural l and positive w with l+w at most k+1, the block is the half-open interval from l to l+w. Task leaves carry distinct coordinates. A fork has two nonempty children with disjoint leaf blocks. Height counts edges, so a terminal has height zero.

**Theorem 1.1 (Every Node of a Balanced Bisection).**

$$0 < w \land l + w \le k + 1 \implies \exists T, \operatorname{Full}\left(T\right) \land \operatorname{leaves}\left(T\right) = \operatorname{interval}\left(l, l + w\right) \land \operatorname{height}\left(T\right) = \operatorname{clog}\left(2, w\right) \land \forall S \in \operatorname{subtrees}\left(T\right), \exists a,b, l \le a < b \le l + w \land \operatorname{leaves}\left(S\right) = \operatorname{interval}\left(a, b\right) \land {a = l \lor b-a \le \operatorname{floorHalf}\left(w\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/BalancedIntervalTree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every subtree has a nonempty adjacent coordinate block inside the original interval. If its left endpoint differs from l, its length is at most the integer floor of w/2. This includes every descendant, not only the root's two children.

For length greater than one, divide into a leading block of length ceil(w/2) and a trailing block of length floor(w/2), then apply the same construction recursively. The child blocks partition the parent interval. The larger half determines the height through the ceiling-logarithm recurrence. A descendant of the trailing half stays inside that half; a nonleading descendant of the leading half is bounded by half the leading length.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/BalancedIntervalTree.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity](FirstRejectionCutCapacity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/TreeMessageRealization](TreeMessageRealization.md)
