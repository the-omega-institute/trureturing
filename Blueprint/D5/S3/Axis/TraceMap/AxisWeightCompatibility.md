# Axis Weight Compatibility

## Abstract

The two axis weights introduced in this repository denote the same function.

The axis weight was introduced twice, eight days apart, in two different strata. Both transcribe the same source formula, reading the expansion face against a golden power and the contraction face against the conjugate power at the same index. They differ only in where the negation sits, so they denote one function.

This document exists because the duplication was found the expensive way. The container the second family was written for already carried a formalization receipt naming the first family, and nothing carried that pointer to the person doing the work; the conflict surfaced only at deposit, after eight modules had been written and frozen.

What is identified here is the weight and nothing else. The two partial sums are not equal as written: one indexes its words from one, the other runs over Zeckendorf indices starting at two. Their exact relation is a separate result, already proved alongside this one, and it carries two shifts rather than one: it reindexes the weight and also raises the depth. Because the first sum uses the smaller reindexing, the two results still do not compose into a bare equality between the sums, and none is asserted.

**Theorem 1.1 (The two axis weights are one function).**

$$\operatorname{t}\left(K\right) = \operatorname{t}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/AxisWeightCompatibility.axisWeight_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unfolding both definitions leaves two exponentials whose exponents differ by moving a negation across a product, which the ring normaliser discharges.

**Theorem 1.2 (The recurrence transports across the identification).**

$$\operatorname{t}\left(K + 2\right) = \operatorname{t}\left(K + 1\right) \cdot \operatorname{t}\left(K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/AxisWeightCompatibility.axisWeight_succ_succ_transported` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rewriting along the identification carries the multiplicative Fibonacci law from one side to the other, so the two recorded recurrences are one fact about one object rather than two independent facts about two.

## References

- Truth anchor: `D5/S3/Axis/TraceMap/AxisWeightCompatibility.axisWeight_eq`
- Truth anchor: `D5/S3/Axis/TraceMap/AxisWeightCompatibility.axisWeight_succ_succ_transported`
- Dependency: [D5/S1/Recurrence/TraceMap](../../../S1/Recurrence/TraceMap.md)
- Dependency: [D5/S3/Axis/AxisTraceRecurrence](../AxisTraceRecurrence.md)
