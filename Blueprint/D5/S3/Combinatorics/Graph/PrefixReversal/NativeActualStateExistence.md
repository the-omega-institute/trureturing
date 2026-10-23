# Actual Native States at Every Order

## Abstract

The native induction constructs one actual cycle with all simultaneous state data at every order at least three.

**Theorem 1.1 (Construct the Complete State for the Supplied Frame).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateExistence.native_actual_state_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateExistence.native_actual_state_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every supplied frame with at least three selected labels and at least three base labels, the induction yields an actual Hamilton cycle in its marked domain. Its joint partition and both restored partitions use that same cycle and retain their literal ports. The state includes the protected-a, remaining-b and selected-c edge invariants. The orientation flags are the stated parity functions of the selected-label count. The third-order base is constructed from its own same-parent eight-piece partition; the successor uses the retained old states to choose its children once and carries their actual walk identities through the parent and boundary updates. The induction preserves the supplied frame rather than replacing it by a frame with only the same label sets. The final full-domain Hamilton cycle is a separate consumer of this state.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateExistence.native_actual_state_exists`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep](NativeActualStrongStateStep.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor](NativeFramePredecessor.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState](NativeJ2ThirdOrderState.md)
