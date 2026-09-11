# Return Seeds Forced by Actual Reachability

## Abstract

Reached disjoint regions with no incoming zero edge require distinct used return slots.

**Theorem 1.1 (A reached zero-closed region has a used return entry).**

Lean statement: `D5/S0/Certificates/SkeletonReturnSeedLowerBound.reached_region_has_used_return`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonReturnSeedLowerBound.reached_region_has_used_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction in the original runTransition semantics shows that neither channel could enter the region if every selected return also avoided it. The conclusion supplies a selected slot, not an arbitrary unused allocation.

**Theorem 1.2 (Every reached zero-indegree state is a return target).**

Lean statement: `D5/S0/Certificates/SkeletonReturnSeedLowerBound.zero_leaf_is_used_return`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonReturnSeedLowerBound.zero_leaf_is_used_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The singleton region of a noninitial state without zero predecessors satisfies the preceding entry theorem. This is the finite leaf obligation used in fixed-zero-map exhaustion.

**Theorem 1.3 (Disjoint reached regions consume distinct slots).**

Lean statement: `D5/S0/Certificates/SkeletonReturnSeedLowerBound.disjoint_return_regions_bound_slots`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/SkeletonReturnSeedLowerBound.disjoint_return_regions_bound_slots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose one used return entering each region. Disjointness makes the selected slots injective, so their number is at most the original slot capacity. Full-carrier reachability in the numerical search must first be justified by exclusion of smaller reachable realizations. No arbitrary padded machine is assumed reachable.

## References

- Truth anchor: `D5/S0/Certificates/SkeletonReturnSeedLowerBound.disjoint_return_regions_bound_slots`
- Truth anchor: `D5/S0/Certificates/SkeletonReturnSeedLowerBound.reached_region_has_used_return`
- Truth anchor: `D5/S0/Certificates/SkeletonReturnSeedLowerBound.zero_leaf_is_used_return`
- Dependency: [D5/S0/Certificates/SkeletonSlotCNF](SkeletonSlotCNF.md)
