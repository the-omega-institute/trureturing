# Advance the Complete Actual State

## Abstract

The same parent joint partition earns both restored orders and all retained edge invariants.

**Theorem 1.1 (Construct the Next Strong State).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep.strong_state_from_same_parent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep.strong_state_from_same_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current joint partition and both actual prior boundary orders earn a complete next state. Its graph map preserves raw vertices, its primary and opposite parity flags exchange, and its distinguished flag flips. The Hamilton property, literal boundary coordinates, all three partitions and all three retained-edge invariants remain attached to the same mapped parent cycle.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep.strong_state_from_same_parent`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion](NativeActualStateJointPromotion.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeFullStateTransport](NativeFullStateTransport.md)
