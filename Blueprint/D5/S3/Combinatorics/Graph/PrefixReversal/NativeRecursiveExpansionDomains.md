# Actual Native Insertion Child Domains

## Abstract

Literal native deletion assigns every supplied cut to exactly one independent insertion child.

**Theorem 1.1 (All Independent Insertion Children).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_child_gap_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_child_gap_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete parent deletion layer is partitioned by the independently specified cyclic insertion gaps of the actual frame base. Each actual parent vertex belongs to one and only one child. A base of length at least three earns orientation separation; parent coverage is a conclusion.

**Theorem 1.2 (Literal Deletion Coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_child_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_child_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting the selected labels from each actual right and left port gives the specific residual child circle and its reverse. The supplyGap function is calculated from the native position: the first k plus one cuts belong to gap zero, and every later position belongs to its literal positive gap.

**Theorem 1.3 (Both Endpoints Belong to Their Child).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_cut_child_domain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_cut_child_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both endpoints of every supplied b cut lie in the independent child calculated by the deletion-coordinate theorem. The conclusion concerns actual configurations, without defining membership from a skeleton edge.

**Theorem 1.4 (The Calculated Owner Is Unique).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_cut_owner_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_cut_owner_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete child-domain uniqueness makes the coordinate computation an equivalence: either endpoint lies in a particular child exactly when its computed supply gap equals that child index. It cannot occur in another child.

**Theorem 1.5 (Exactly the Special-Child Positions).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_special_child_cut_indices`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_special_child_cut_indices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The special insertion child contains precisely supplier positions zero through k. This follows from the actual owner computation and the explicit native index map, without supplying a target cut count.

**Theorem 1.6 (One Actual Cut per Ordinary Child).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_other_child_unique_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_other_child_unique_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each positive insertion gap has one and only one actual supplier cut, at position k plus its gap index. Both existence and uniqueness follow from literal tuple deletion and the computed child owner.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_child_gap_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_other_child_unique_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_special_child_cut_indices`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_child_coordinates`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_cut_child_domain`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.native_supply_cut_owner_iff`
- Dependency: [D5/S3/Combinatorics/CircularWords/CyclicInsertionGap](../../CircularWords/CyclicInsertionGap.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/InsertionLayerPartition](InsertionLayerPartition.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveSupply](NativeRecursiveSupply.md)
