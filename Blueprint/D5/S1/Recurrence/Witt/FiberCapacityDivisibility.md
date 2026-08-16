# Fiber Capacity and Divisibility

## Abstract

A consecutive fiber polynomial has the factor X plus one exactly when its capacity is even.

**Theorem 1.1 (Even capacity is equivalent to the alternating factor).**

$$\forall m, c \in \mathbb{N}, (1+X) \mid X^{m} \sum_{i<c} X^{i} \iff 2 \mid c$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Witt/FiberCapacityDivisibility.one_add_x_dvd_fiber_polynomial_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation at minus one turns the consecutive fiber polynomial into an alternating geometric sum. Its value vanishes exactly at even capacity, independently of the starting exponent.

The proof combines Mathlib's linear-factor criterion, polynomial geometric-sum evaluation, and exact parity formula for a geometric sum at minus one. No duplicate factor theorem is introduced.

This closes only the capacity-divisibility mechanism in source theorem 6.49. It does not assert the explicit g-row identities, the Witt exponent tables, the finite-window row-four tail, or the Sturmian classification stated elsewhere in that atom.

## References

- Truth anchor: `D5/S1/Recurrence/Witt/FiberCapacityDivisibility.one_add_x_dvd_fiber_polynomial_iff`
