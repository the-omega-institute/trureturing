# Finite Product Threshold Pruning

## Abstract

Finite Product Threshold Pruning.

**Theorem 1.1 (Simultaneous bounds for a feasible reduction).**

Lean statement: `D5/S1/Digit/Admissibility/FiniteProductThresholdPruning.exists_threshold_pruning`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Admissibility/FiniteProductThresholdPruning.exists_threshold_pruning` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be a natural number at least two and let A be any finite vector of natural capacities with product of A(i) + 1 at least q. There exists a vector a with a(i) at most A(i) for every coordinate and product of a(i) + 1 still at least q. Every entry of a is at most q minus one, the number of its positive entries is at most the least h with q at most two to the power h, and its product is strictly less than twice q. Choose a feasible vector minimizing the sum of its capacities. Lowering any positive capacity then makes the product less than q. Truncating an oversized entry and deleting a positive coordinate give the entry and support bounds; lowering a positive entry by one gives the product bound.

## References

- Truth anchor: `D5/S1/Digit/Admissibility/FiniteProductThresholdPruning.exists_threshold_pruning`
