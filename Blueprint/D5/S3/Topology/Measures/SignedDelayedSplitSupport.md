# Signed source limits and delayed columns

## Abstract

Signed source limits and delayed columns

**Theorem 1.1 (A common source limit for every signed lift selection).**

Lean statement: `D5/S3/Topology/Measures/SignedDelayedSplitSupport.common_source_on_split`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedDelayedSplitSupport.common_source_on_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split is closed with an onto old projection. Its true sheet lies over Q, disjoint from the source clopen P. The source signed measures have total variation at most one, are carried by P and by their clopen supports, and satisfy old every-choice weak convergence along J. On an infinite subset M of J, both the old coordinates and the new Boolean coordinate are eventually constant on whole support fibres. A genuine norm-preserving lift supplies a reference. The conclusion selects one signed measure on this same split, with total variation at most one and regular positive and negative Jordan parts, to which every norm-preserving lift selection converges along M.

**Theorem 1.2 (One literal delayed column after a finite ordered history).**

Lean statement: `D5/S3/Topology/Measures/SignedDelayedSplitSupport.exists_literal_delayed_column`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/SignedDelayedSplitSupport.exists_literal_delayed_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An infinite target pool has whole fibres converging to the specified point z. The target signed measures are the prescribed Dirac measures. Auxiliary rows retain their signed norm-preserving lifts, support nullity, reference convergence, disjoint supports and whole-support coordinate constancy. The construction fixes the earlier finite exclusion, chooses the next target index, and defines H literally as the inverse image of V(n) intersect Q minus that exclusion. It then fixes finite tests and chooses auxiliary indices. The resulting ordered column satisfies the original signed finite estimates, its entire target fibre lies in H, and all selected auxiliary supports avoid z. SignedDelayedSplit consumes this column in its parity construction and consumes the common source limit in its internal delayed split. These are constituent proofs of the compact metric local construction, with no ordinal-history or final-cube assertion.

## References

- Truth anchor: `D5/S3/Topology/Measures/SignedDelayedSplitSupport.common_source_on_split`
- Truth anchor: `D5/S3/Topology/Measures/SignedDelayedSplitSupport.exists_literal_delayed_column`
- Dependency: [D5/S3/Topology/Measures/SignedSplitSuccessor](SignedSplitSuccessor.md)
