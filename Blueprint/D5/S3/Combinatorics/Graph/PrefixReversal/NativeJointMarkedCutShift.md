# Exact Native Marked Cut Sets

## Abstract

Exact Native Marked Cut Sets.

**Theorem 1.1 (Shift One Complete Cut Group).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.native_frame_marked_cuts_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.native_frame_marked_cuts_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a supplied frame with base A followed by u, every positive cut in nextFrame is the same actual edge as a prior cut. The complete new group is the prior group with exactly its new zero edge inserted; no unlisted index is assumed.

**Theorem 1.2 (Shift Both Marked Orders Together).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.native_joint_marked_cuts_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.native_joint_marked_cuts_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two prior selected orders with the same remaining base A followed by u, the union of both next cut groups equals the union of both prior groups together with the two actual new zero edges. The next orders exchange the prior orders, preserving literal configurations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.native_frame_marked_cuts_shift`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.native_joint_marked_cuts_shift`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates](NativeMarkedStepCoordinates.md)
