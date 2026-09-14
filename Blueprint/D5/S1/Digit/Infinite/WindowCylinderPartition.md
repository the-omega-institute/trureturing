# The Cylinder Partition of Legal Digit Windows

## Abstract

The Cylinder Partition of Legal Digit Windows.

**Theorem 1.1 (Closed intervals and oriented circle cuts).**

Lean statement: `D5/S1/Digit/Infinite/WindowCylinderPartition.window_cylinder_partition`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/WindowCylinderPartition.window_cylinder_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete a legal window by appending a zero when its last digit is one. The resulting return-block word parametrizes its cylinder by arbitrary legal tails. The signed values form a closed affine interval of length alpha to the completed digit length. For each positive window length these intervals cover the full value range and have pairwise disjoint interiors. Their circle boundaries are precisely the negative golden phases indexed from one through the Fibonacci window count. Each cylinder contains the full preimage of its open arc, the positive-side stream at its left endpoint, and the negative-side stream at its right endpoint. The two streams at an indexed phase have different windows exactly when the index does not exceed the window count. At the circle seam the positive and negative streams are the lower and upper alternating streams, respectively.

## References

- Truth anchor: `D5/S1/Digit/Infinite/WindowCylinderPartition.window_cylinder_partition`
- Dependency: [D5/S1/Digit/Infinite/WindowSuccessorGraph](WindowSuccessorGraph.md)
