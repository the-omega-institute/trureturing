# Finite separation and synthesis for bounded binary recurrences

## Abstract

An authentic initial block of 2d bits determines every digit of any binary forward-recurring stream of order at most d. Fixed finite enumeration recovers a generator for that behavior.

**Theorem 1.1 (Sufficient initial comparison and first matching forward generator).**

$$(\forall i<2d, s_{i}=t_{i}) \implies (\forall i, s_{i}=t_{i})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrence.bounded_binary_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both streams are actual Boolean sequences satisfying a forward binary recurrence at every index, with possibly different orders and coefficients. Both orders are at most d. The initial block starts at index zero and the recurrence is the finite coefficient dot product reduced modulo two.

The monic shift operator for each stream annihilates it. The two shift operators commute, so their product annihilates the difference. Its highest shift is the sum of the two orders, at most 2d. If that many initial differences vanish, the highest-term equation determines every later difference to be zero; the calculation never runs backward.

Prepend zero taps to obtain an order-d row without changing the predicted terminal digit. The search enumerates all $2^{d}$ Boolean rows in a fixed mask order, installs the same first d observed bits into each one, and returns the first row whose first 2d digits match. A lawful word guarantees at least one match; the selected generator agrees at every index. At d=0 this gives the zero generator.

No minimality or invertibility is required: zero taps, transients and singular recurrences are allowed. This determines output behavior, not private coefficients, state, or original seed presentation. No sharpness, sampling-price or optimal-running-time claim is made.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LocalWiring/BoundedBinaryRecurrence.bounded_binary_recurrence`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LocalWiring/PublicRowSeedReadiness](PublicRowSeedReadiness.md)
