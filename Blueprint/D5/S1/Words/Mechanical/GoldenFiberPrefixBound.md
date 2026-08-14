# Golden Fiber Prefix Bound

## Abstract

A finite positive-indexed golden-fiber prefix has an elementary linear upper bound.

**Theorem 1.1 (Golden-fiber prefixes satisfy the linear bound).**

$$\forall T\in\mathbb{N},\ \sum_{n=1}^{T} f_n \le \varphi T + 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/GoldenFiberPrefixBound.golden_fiber_prefix_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prefix length T, the sum of the positive-indexed golden-fiber letters f_n from n = 1 through T is at most phi times T plus two. The integer-valued sum is compared in the real numbers.

The repository's exact golden_fiber_prefix_count identity is the strictly stronger reusable result. After rewriting by that identity, Mathlib's Int.floor_le and Real.goldenRatio_lt_two bounds close the inequality; no prefix count is reproved.

This is an honest partial closure of only the explicit prefix-sum bound in the leading elementary chain. The polynomial maximum and evaluation claims, Bernstein derivative estimate, peak lower bound, zero-free disks, numerical checks, status change, and localization discussion remain unresolved and are not asserted here.

## References

- Truth anchor: `D5/S1/Words/Mechanical/GoldenFiberPrefixBound.golden_fiber_prefix_sum_le`
- Dependency: [D5/S1/Words/Mechanical/GoldenFiberPrefixCount](GoldenFiberPrefixCount.md)
