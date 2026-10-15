# Restoring Actual Cut Groups of the Same Cycle

## Abstract

The same supplied cycle earns the exact regrouped edge inventories for half restoration.

All walks and partitions concern the literal supplied cycles. The prior cycle can be included in a larger graph without assuming that it is Hamiltonian there. The current boundary outputs keep their actual walk identities and exact inventories.

**Theorem 1.1 (Recover the Single-Order Retained Inventory).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_restored_single_order_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_restored_single_order_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two disjoint cut groups and actual joint and single-order filtered inventories refer to the same supplied cycle. Restoring the opposite cut group earns the single-order edge permutation from the actual joint edges followed by those restored cuts.

**Theorem 1.2 (Recover the Prior Actual Regroupings).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_prior_single_order_partition_inventories`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_prior_single_order_partition_inventories` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual joint and single-order families have support permutations to the same nonrepeating cycle tail. They yield simple single-order support, the exact joint-support permutation and the exact restored-edge permutation needed by the next boundary step.

**Theorem 1.3 (Isolate the New Opposite-Order Cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_joint_half_cut_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_joint_half_cut_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint retained inventory and actual cut membership partition the complete source cycle edge list. One supplied seam in the restored group is isolated after the other restored cuts. Disjointness proves that this seam is absent from the still-deleted group and that the remaining restored cuts stay disjoint.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_joint_half_cut_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_prior_single_order_partition_inventories`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.actual_restored_single_order_inventory`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate](ActualJointPartitionUpdate.md)
