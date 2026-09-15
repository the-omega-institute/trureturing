# Rational Capacity Tail Realization

## Abstract

Exact rational tail fillings produce every extended nonnegative total reading.

Let g be a row of positive natural denominators and A a row of natural capacities. A total state has natural coordinates x_n at most A_n; a finite state additionally has finite support. The finite reading is the sum of x_n/g_n, and the extended total reading is the supremum of the inclusive partial sums through N. The chapter's denominator row is g_n = fib(n+2).

**Theorem 1.1 (Exact rational tails and infinite tail mass).**

Lean statement: `D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.cofinal_capacity_rational_tail_filling`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.cofinal_capacity_rational_tail_filling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose one positive real threshold epsilon works for every positive modulus d and every cutoff N: some index n greater than N has d dividing g_n and A_n/g_n at least epsilon. Then every nonnegative rational q is the exact reading of a finite legal state supported strictly after N. Split q into k equal rational parts a/b at most epsilon, choose k distinct suitable indices, and put a(g_n/b) at each selected coordinate. Conversely, exact rational filling alone forces every tail capacity sum to be infinite, since the tail dominates finite states with arbitrarily large integer readings.

**Theorem 1.2 (Every extended nonnegative reading).**

Lean statement: `D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.rational_tail_filling_full_range`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.rational_tail_filling_full_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every nonnegative rational fills every tail exactly, the total reading maps the space of total capacity states onto the extended nonnegative reals. For a finite target, take increasing nonnegative rational approximations starting at zero. Fill each increment beyond the preceding finite support and a successively increasing cutoff. The resulting finite states increase coordinatewise and each coordinate eventually stabilizes. Their stabilized total state has all partial sums bounded by the target, while its total dominates every approximating reading, so equality follows. For infinity, take the capacity corner: its total dominates an infinite tail mass. The resulting state may have infinite support.

## References

- Truth anchor: `D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.cofinal_capacity_rational_tail_filling`
- Truth anchor: `D5/S3/Arith/GoldenResource/RationalCapacityTailRealization.rational_tail_filling_full_range`
- Dependency: [D5/S3/Analytic/WeightedCapacity/DyadicTailFilling](../../Analytic/WeightedCapacity/DyadicTailFilling.md)
