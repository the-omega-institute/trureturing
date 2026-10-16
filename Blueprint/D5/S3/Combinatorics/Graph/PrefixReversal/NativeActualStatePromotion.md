# Promote the Original Actual P State

## Abstract

The actual P opening is recovered from the original retained P state and the same parent.

**Theorem 1.1 (Recover the Actual P Opening Inventory).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.original_state_p_opening_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.original_state_p_opening_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The P opening used by the parent has the full support of its original P state and precisely that state cycle with the literal supplier edge removed. Restoring both old cut groups yields its exact joint-edge inventory.

**Theorem 1.2 (Split the Original Distinguished P Path).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.original_state_p_joint_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.original_state_p_joint_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The retained edge invariants force the literal two-edge P prefix on the distinguished path. Removing the supplier edge produces the exact inventory needed by the later closed-parent joint update; no new P walk is chosen.

**Theorem 1.3 (Keep the Saved Parent Chain Attached).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.same_parent_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.same_parent_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The saved child openings form the literal native c-linked chain from the retained parent base to its saved P opening, with the actual closing edge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.original_state_p_joint_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.original_state_p_opening_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion.same_parent_chain`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualPJointPrefix](NativeActualPJointPrefix.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers](NativeActualStateSuppliers.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory](../Walks/ActualJointHalfCutInventory.md)
