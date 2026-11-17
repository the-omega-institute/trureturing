# Twenty Point Slice

## Abstract

Twenty Point Slice

This module records the exact actual twenty-vertex slice telescope for the Hong–Wu–Xia Section 7 Problem 2 branch. The support is induced in an arbitrary Boolean cube and carries original Huang balance, twenty vertices, degrees two or three, exactly ten degree-two vertices, and actual degree-two independence. Girth is derived from balance.

The compiled local reduction constructs the cube-parity bipartition, derives girth at least eight, proves that the induced high graph has five edges, and reduces the parity counts to (10,10;5,5), (11,9;8,2), or the swapped orientation. It does not assume connectivity, a compressed graph, labels, a cycle classification, a coordinate normal form, or a signed-path result.

The five-vertex classification, actual coordinate transport, and Huang-sign contradiction remain open producer work. The unsigned abstract twenty-vertex graph is not used as an actual cube countermodel.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal proposition quantifies over every ambient dimension, every finite actual support, and actual bipartition sides. Its local hypotheses are support cardinality twenty, degree type two or three, exactly ten actual degree-two vertices, actual degree-two independence, and original IsBalanced.

**Theorem 1.2 (actual twenty-point slice data).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.actual_twenty_point_slice_data`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.actual_twenty_point_slice_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

From claim, BalancedCubeGirth.eight_le_egirth supplies girth at least eight; actual low/high incidence counting supplies five high-high edges; and the constructed cube-parity bipartition supplies the three displayed parity alternatives. The final obstruction is not claimed here.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.actual_twenty_point_slice_data`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.claim`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice](EighteenPointSlice.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting](GirthSliceCounting.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph](SymmetricHighGraph.md)
