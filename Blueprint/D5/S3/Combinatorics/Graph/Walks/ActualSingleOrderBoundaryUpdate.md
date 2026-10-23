# Updating Actual Single-Order Boundaries

## Abstract

Literal replacement of the old joint path yields exhaustive actual boundaries of one supplied current cycle.

All walks and partitions concern the literal supplied cycles. The prior cycle can be included in a larger graph without assuming that it is Hamiltonian there. The current boundary outputs keep their actual walk identities and exact inventories.

**Theorem 1.1 (Restore the Second Q Cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.actual_single_order_boundary_update`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.actual_single_order_boundary_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual old boundary route passes through the distinguished joint path. Replace that path by the three actual current joint walks and restore their second Q cut. Source support and edge inventories earn two simple boundary walks, complete unique vertex coverage, exact filtered edges and the complete updated endpoint-pair set. All old boundary pieces outside this route are retained.

**Theorem 1.2 (Restore the First Q Cut).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.actual_single_order_first_cut_boundary_update`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.actual_single_order_first_cut_boundary_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restoring the first Q cut instead joins the reversed middle walk to the reversed first walk on the other side. The output again gives two literal simple boundary walks, the full current-cycle vertex partition, exact retained edges and the earned endpoint update. The final walk identities expose the actual construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.actual_single_order_boundary_update`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.actual_single_order_first_cut_boundary_update`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointEndpointPairs](ActualJointEndpointPairs.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate](ActualJointPartitionUpdate.md)
