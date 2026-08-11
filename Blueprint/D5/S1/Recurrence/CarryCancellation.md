# Recurrence Carry Cancellation

## Abstract

A fixed-width recurrence makes a consecutive block and its carry digit equal in weight.

**Theorem 1.1 (A recurrence redeems its forbidden consecutive block).**

$$w(s+r) = \sum_{i<r} w(s+i)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/CarryCancellation.recurrence_carry_preserves_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite digit state carries natural multiplicities, while an arbitrary additive sequence assigns weights to positions. The local redex occupies the consecutive positions s through s+r-1, and its carry image occupies only position s+r. The recurrence hypothesis identifies their weights. Additivity then preserves the value after adjoining any untouched state.

Widths two and three give the Fibonacci and Tribonacci cancellation patterns once their respective recurrences are supplied. Pinned Mathlib provides Finsupp.weight, Finsupp.weight_single, finite-sum additivity, and Nat.fib_add_two. Searches found no fixed-width recurrence-carry theorem and no Tribonacci declaration, so the uniform local rewrite theorem is new proof content rather than a thin wrapper.

## References

- Truth anchor: `D5/S1/Recurrence/CarryCancellation.recurrence_carry_preserves_weight`
