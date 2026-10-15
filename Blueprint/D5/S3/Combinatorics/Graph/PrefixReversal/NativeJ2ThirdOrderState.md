# Initialize the Complete Third-Order State

## Abstract

The same actual J2 outer parent initializes every field of the full third-order induction state.

**Theorem 1.1 (Transport the Same Parent and Its Eight Actual Paths).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.native_j2_parent_third_order_state`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.native_j2_parent_third_order_state` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal eight-piece joint partition is transported along the bijection that preserves every configuration. Both restored partitions and the three retained-edge invariants belong to that same cycle. The resulting third-order state has primary odd, opposite even and the primary distinguished far endpoint.

**Theorem 1.2 (Construct the Complete State for Every Third-Order Frame).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.native_third_order_state_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.native_third_order_state_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every supplied frame with three selected labels and at least three base labels receives a full actual state. Its predecessor supplies native P and Q witnesses. Reversing the selected order twice returns the original frame, so the construction retains the precise supplied frame and all three orientation flags. This is the base consumed by the all-order state induction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.native_j2_parent_third_order_state`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.native_third_order_state_exists`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualInductionState](NativeActualInductionState.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor](NativeFramePredecessor.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentRetention](NativeJ2ParentRetention.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts](NativeOppositeMarkedPorts.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeThirdOrderBoundaryBase](NativeThirdOrderBoundaryBase.md)
