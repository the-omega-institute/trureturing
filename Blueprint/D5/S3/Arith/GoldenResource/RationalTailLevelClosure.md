# Rational Tail Level Closure

## Abstract

Exact rational tails determine the closures of finite capacity levels.

Let g be a row of positive natural denominators and A a row of natural capacities. Total states have coordinates x_n at most A_n, and finite states have finite support. Their rational reading is the sum of x_n/g_n; the extended total is the supremum of the inclusive real partial sums. Both carriers use the coordinate topology, with the finite states carrying the subspace topology. The chapter's denominator row is g_n = fib(n+2).

**Theorem 1.1 (Sharp closures and trivial levels).**

Lean statement: `D5/S3/Arith/GoldenResource/RationalTailLevelClosure.rational_tail_level_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RationalTailLevelClosure.rational_tail_level_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose every nonnegative rational can be filled exactly by a legal finite state supported beyond any prescribed cutoff. For each nonnegative rational c, the closure of the finite-state level c in the full product is exactly the set of states whose extended total is at most c, and its closure in the finite-state carrier is exactly the set whose reading is at most c. A state in the sublevel can be approximated while preserving any finite prefix: fill the rational deficit after that prefix. Conversely, a partial sum exceeding c gives a coordinate neighborhood disjoint from the level. Every positive rational level is nonempty and is not closed in either carrier, because zero is in its closure and outside the level. For every capacity row, without the tail filling assumption, both zero levels consist exactly of the zero state. Negative and irrational finite real levels and their closures in both carriers are empty.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/RationalTailLevelClosure.rational_tail_level_closure`
- Dependency: [D5/S3/Arith/GoldenResource/RationalCapacityTailRealization](RationalCapacityTailRealization.md)
