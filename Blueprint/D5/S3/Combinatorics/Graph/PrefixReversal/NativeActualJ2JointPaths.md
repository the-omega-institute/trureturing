# Same-Cycle Native Joint Components

## Abstract

Six actual native components partition the support and uncut edges of the same supplied cycle.

The native J2 six-component theorem specifies the endpoint table independently of a selected cycle. The conclusions below lift those paths to a domain whose actual vertices are precisely the full F2 domain. The same supplied Hamiltonian cycle and its exact native inventory are used throughout; these results do not assert an all-order recursive construction.

**Theorem 1.1 (Six Components of the Supplied Cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.native_actual_j2_joint_paths`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.native_actual_j2_joint_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least five, the six actual simple paths keep their literal componentStartPort and componentFinishPort endpoints. Their supports cover every domain vertex once and are a permutation of the supplied cycle support tail. Their concatenated edges are a permutation of exactly the supplied cycle edges outside the six independent marked cuts. Every marked cut belongs to that same cycle. No support partition or target retained-edge certificate is assumed.

**Theorem 1.2 (Preserve the Same Components in an Arbitrary Frame).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.native_actual_j2_frame_joint_paths`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.native_actual_j2_frame_joint_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left label relabelling maps the six actual components into the complete independent domain of any two-label supply frame. The indexed endpoint table, simple-path property, full support permutation and exact edge permutation are retained against the same mapped cycle. The six cuts are mapped pointwise by the same graph isomorphism.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.native_actual_j2_frame_joint_paths`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.native_actual_j2_joint_paths`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Components](NativeJ2Components.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2FrameInventory](NativeJ2FrameInventory.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualPartitionTransport](../Walks/ActualPartitionTransport.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory](../Walks/ActualPathFamilyInventory.md)
