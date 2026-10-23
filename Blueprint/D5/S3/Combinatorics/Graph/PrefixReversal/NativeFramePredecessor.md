# An Actual Predecessor for Every Supplied Frame

## Abstract

An Actual Predecessor for Every Supplied Frame.

**Theorem 1.1 (Recover Every Next Frame).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor.native_frame_predecessor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor.native_frame_predecessor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every supplied frame with k+1 selected labels is exactly nextFrame of a prior k-label frame. The prior base is the supplied base followed by the first supplied selected label. The terminal is unchanged, the prior base is one label longer, and for k at least two the last two protected selected labels retain their identities. This proves that induction covers arbitrary supplied frames rather than only generated frames.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor.native_frame_predecessor`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates](NativeMarkedStepCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels](NativeProtectedLabels.md)
