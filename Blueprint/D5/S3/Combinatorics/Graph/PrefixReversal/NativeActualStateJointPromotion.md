# Promote the Same Parent Joint Partition

## Abstract

The new joint partition uses the actual P opening, actual Q fragments and saved parent cycle.

**Theorem 1.1 (Earn the Current Joint Partition on the Saved Parent).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion.current_joint_from_same_state_parent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion.current_joint_from_same_state_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original P split and the three Q fragments are joined through the saved child chain. The resulting joint partition lies on the same parent cycle; its two cut groups are disjoint, have their literal native images, and erase to the opposite old cut groups under the actual P lift.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion.current_joint_from_same_state_parent`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJointUpdate](NativeActualJointUpdate.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateQPromotion](NativeActualStateQPromotion.md)
