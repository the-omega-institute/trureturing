# Preserve Protected a and Remaining b Edges Through Native Recursion

## Abstract

Preserve Protected a and Remaining b Edges Through Native Recursion.

**Theorem 1.1 (Terminal Labels Distinguish Undirected b Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_b_edges_distinct_terminals`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_b_edges_distinct_terminals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both ends of an actual b edge keep the same terminal label. Actual undirected b edges with distinct terminal labels therefore differ, regardless of orientation.

**Theorem 1.2 (Remaining-Terminal b Edges Are Uncut).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_remaining_b_not_special_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_remaining_b_not_special_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual b edge in the special native domain whose terminal differs from the supplier terminal cannot be any supplier cut.

**Theorem 1.3 (Special Joining Retains an Actual Remaining b Edge).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_special_path_keeps_remaining_b`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_special_path_keeps_remaining_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact uncut-piece inventory of a supplied cycle and the literal joined chain preserve every actual previous b edge with a terminal different from the supplier terminal.

**Theorem 1.4 (Ordinary Opening Retains Remaining b Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_other_path_keeps_remaining_b`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_other_path_keeps_remaining_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supplied ordinary complement path removes exactly its supplier b edge. An actual previous b edge with a different terminal therefore belongs to that same path.

**Theorem 1.5 (The Parent Retains Every Actual Child-Path Edge).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_child_path_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_child_path_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the literal closed parent edge chain associated with the supplied lifted child paths, every actual edge of each child path occurs in the raw edge list of that same parent cycle. No new child path or cycle is selected.

**Theorem 1.6 (Earn the Parent Remaining b Invariant).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_remaining_b`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_remaining_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unique native child-layer partition and the actual parent chain transfer the supplied child-path b retention law to the same parent cycle. The terminal guard excludes both the old selected labels and the supplier terminal.

**Theorem 1.7 (Full Reversal Changes the Terminal).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_changes_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_changes_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an actual native configuration at the stated dimension, the full reversal a changes the terminal label because the first and last positions are distinct and the configuration is injective.

**Theorem 1.8 (Actual a Edges Differ from Supplier b Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_edge_ne_b_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_edge_ne_b_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two ends of an a edge have different terminal labels while both ends of a b edge have the same label. The resulting inequality concerns undirected edges.

**Theorem 1.9 (No Actual a Edge Is a Supplier Cut).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_not_special_cut`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_not_special_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual a edge in the native special child differs from each supplier b cut, independently of the protected terminal pair.

**Theorem 1.10 (Special Joining Retains Previous a Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_special_path_keeps_a`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_special_path_keeps_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only supplier b edges are removed from the supplied special cycle. The exact uncut-piece inventory and joined chain therefore preserve every previous actual a edge.

**Theorem 1.11 (Ordinary Opening Retains Previous a Edges).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_other_path_keeps_a`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_other_path_keeps_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An ordinary complement path removes its single supplier b edge. Its exact inventory preserves every actual a edge of the supplied child cycle.

**Theorem 1.12 (Earn the Parent Protected a Invariant).**

Lean statement: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_protected_a`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_protected_a` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native child-layer partition and actual parent edge chain transfer each supplied child-path a retention law to this same parent cycle. The guard excludes exactly the fixed protected terminal pair; previously missing a edges are not claimed to have been restored.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_changes_terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_edge_ne_b_edge`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_a_not_special_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_b_edges_distinct_terminals`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_other_path_keeps_a`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_other_path_keeps_remaining_b`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_child_path_edges`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_protected_a`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_parent_cycle_keeps_remaining_b`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_remaining_b_not_special_cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_special_path_keeps_a`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.native_special_path_keeps_remaining_b`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates](NativeMarkedStepCoordinates.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveCycleStep](NativeRecursiveCycleStep.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges](../Walks/ActualRetainedEdges.md)
