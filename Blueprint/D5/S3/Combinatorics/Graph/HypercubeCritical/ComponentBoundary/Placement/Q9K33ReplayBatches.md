# Intermediate consequences of the contact certificate

## Abstract

Named intermediate consequences reduce the memory needed to replay a resolution proof.

**Definition 1.1 (Replay in batches).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches.replay`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches.replay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Lean replay uses the resolution hints in their original order. When facts are used in a later batch, a theorem records that they follow from the original clauses. The kernel checks each such theorem and the final contradiction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches.replay`
