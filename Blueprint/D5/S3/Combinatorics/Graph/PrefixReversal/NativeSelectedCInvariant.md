# Classify Every Retained and New Native c Edge

## Abstract

Classify Every Retained and New Native c Edge.

**Theorem 1.1 (Special Joining Adds Only a Newly Selected c Label).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_special_path_c_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_special_path_c_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the exact uncut-piece inventory of one previous special cycle and the literal native port coordinates of the joined piece finishes, every c edge of the actual joined special path has a terminal among the previous selected labels or the supplier terminal. Old edges and newly inserted seams are handled separately.

**Theorem 1.2 (An Ordinary Opening Adds No Edge).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_other_path_c_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_other_path_c_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordinary child path with the exact one-supplier-cut complement inventory inherits the supplied previous cycle classification of c edges. The conclusion concerns every actual edge of the chosen complement path.

**Theorem 1.3 (Exhaust Every c Edge of the Same Parent Cycle).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_parent_cycle_c_labels`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_parent_cycle_c_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete literal parent edge chain consists of the actual lifted child-path edges and its outer seams. Supplied classifications for those same child paths imply that every c edge of this parent cycle has a terminal among the old selected labels or the supplier terminal. The child association, root coordinate and chain inventory remain explicit premises.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_other_path_c_labels`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_parent_cycle_c_labels`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeSelectedCInvariant.native_special_path_c_labels`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention](NativeMarkedCutRetention.md)
