# Partial Sum Bridge

## Abstract

The admissible-word sum and the Zeckendorf-range sum agree under one depth shift.

Two formalizations of the same partial sum exist in this repository, written eight days apart under different index conventions. One sums over the subsets of an initial segment that contain no two adjacent indices, weighting each index one above its position. The other sums over an initial segment of the naturals, weighting each by the product over its Zeckendorf indices, which start at two.

They are not interchangeable as written: the depths differ by one and so do the weight indices. Numerical probes showed the two shifts before this theorem existed; the theorem is what makes a statement about one side a statement about the other.

The proof builds no Zeckendorf bijection. Both sides already carry the same two step recursion as public theorems and their two base values agree, so strong induction closes it. The two frozen modules the bridge spans are untouched.

**Theorem 1.1 (The two partial sums agree under both shifts).**

$$\operatorname{wordSum}\left(\operatorname{shiftedWeight}\left(\right), K\right) = \operatorname{axisPartialSum}\left(K + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/TraceMap/PartialSumBridge.wordSum_eq_axisPartialSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Shifting the weight index by two and the depth by one carries one sum onto the other. Cutting either shift makes the module fail to build, so both carry weight.

## References

- Truth anchor: `D5/S3/Axis/TraceMap/PartialSumBridge.wordSum_eq_axisPartialSum`
- Dependency: [D5/S1/Recurrence/TraceMap](../../../S1/Recurrence/TraceMap.md)
- Dependency: [D5/S3/Axis/AxisPartialSum](../AxisPartialSum.md)
