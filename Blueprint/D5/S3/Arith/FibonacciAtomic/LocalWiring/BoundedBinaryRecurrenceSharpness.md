# Sharp uniform prefix separation for bounded binary recurrences

## Abstract

For each shorter cut, two actual binary recurrence streams share the observed prefix but give opposite next digits. Together with sufficiency, this makes twice the order bound the least uniform separating length.

**Theorem 1.1 (Lawful witnesses for every shorter prefix).**

$$(1\le d \land 0\le v<2d) \implies \exists s,t \in \mathcal{R}_{d}, (\forall i<v, s_{i}=t_{i}) \land s_{v}\neq t_{v}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrenceSharpness.bounded_binary_recurrence_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive public bound d and each natural cut v below 2d, the executable constructor gives an actual pair of forward-recurring Boolean streams of order at most d. They have equal outputs at every index before v and first differ exactly at v.

Below d, compare zero with a single impulse at v. The impulse has an all-zero-tap presentation of order v+1. For d≤v<2d, put r=v−d; compare an impulse at r with the d-periodic stream supported on residue r. The periodic row copies its zero-lag input forward by d. Before v both streams have their sole one at r, and only the periodic stream has a one at v.

The uniform separation characterization uses the frozen sufficient bound: for positive d a length works for all legal pairs exactly when it is at least 2d. It does not require one fixed pair to oppose all shorter cuts, infer any individual stream's least order, or price paid observations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrenceSharpness.bounded_binary_recurrence_sharpness`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrence](BoundedBinaryRecurrence.md)
