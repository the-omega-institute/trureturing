# Actual Coordinates of the Marked Step

## Abstract

Native full tuples earn the next marked coordinates and independent child ownership.

**Theorem 1.1 (Literal Rotation Shifts Every Positive Mark).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_marked_index_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_marked_index_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every supplied frame and a last base label u, the right and left native ports of nextFrame at index i+1 equal the old ports at index i. The proof computes the full permutation tuple, so the equality identifies actual configurations for all natural indices.

**Theorem 1.2 (The Actual New Zero Cut Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_q_index_zero_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_q_index_zero_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer frame left-zero vertex takes an a-generator step to the next frame right-zero vertex, then a b-generator step to its left-zero vertex. Both equalities concern the full native configurations.

**Theorem 1.3 (The Actual Final P Supplier Cut).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_p_parent_cut_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_p_parent_cut_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old left-zero configuration takes its a step to the final outer supplier right port, whose b step reaches the supplier left port. That same old configuration equals nextFrame left port one.

**Theorem 1.4 (Earn Both Endpoint Child Domains).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_new_marked_cut_domains`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_new_marked_cut_domains` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a sufficiently long remaining base, the new mark zero has both endpoints in outer child zero, and every positive new mark has both endpoints in the final outer child. The independent Layer domain is earned by literal tuple deletion and circle rotation.

**Theorem 1.5 (Exact Marked Cut Ownership).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_new_marked_cut_owner_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_new_marked_cut_owner_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent disjoint child partition upgrades endpoint membership to an iff: both endpoints of a new mark belong to outer child j exactly when j is zero for mark zero or the final gap for a positive mark. It excludes every third child without assuming a future walk.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_marked_index_shift`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_new_marked_cut_domains`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_new_marked_cut_owner_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_p_parent_cut_prefix`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.native_q_index_zero_prefix`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialChildAssembly](NativeSpecialChildAssembly.md)
