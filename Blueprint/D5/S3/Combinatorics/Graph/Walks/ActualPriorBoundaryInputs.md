# Recovering Actual Prior Boundary Inputs

## Abstract

Verified partitions of one supplied prior cycle earn the literal route inputs for the next boundary update.

All walks and partitions concern the literal supplied cycles. The prior cycle can be included in a larger graph without assuming that it is Hamiltonian there. The current boundary outputs keep their actual walk identities and exact inventories.

**Theorem 1.1 (Recover the Actual Primary Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.actual_prior_primary_boundary_inputs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.actual_prior_primary_boundary_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual joint and primary partitions of the same prior cycle earn simplicity, exact support and edge regroupings and a literal primary factorization beginning with the distinguished joint walk. Its returned tail is an actual simple walk.

**Theorem 1.2 (Recover the Actual Opposite Crossing Prefix).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.actual_prior_opposite_boundary_inputs`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.actual_prior_opposite_boundary_inputs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual old seam joins the reverse crossing piece to the distinguished joint path. The same prior cycle inventories earn every edge of that prefix, its nonrepeating support and its literal position at the start of the supplied opposite boundary, including a simple remaining tail.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.actual_prior_opposite_boundary_inputs`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.actual_prior_primary_boundary_inputs`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory](ActualJointHalfCutInventory.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix](ActualPathRecoveryPrefix.md)
