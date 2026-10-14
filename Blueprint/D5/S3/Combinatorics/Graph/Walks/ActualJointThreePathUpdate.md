# Recombining Three Actual Joint Paths

## Abstract

Literal P and Q fragments and an actual connector form three new simple paths with exact inventories.

The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.

**Theorem 1.1 (Construct the Three New Joint Paths).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate.actual_joint_three_path_update`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate.actual_joint_three_path_update` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual distinguished path starts with the two supplied edges, and the actual route has been split into three supplied fragments. The real connector and seam explicitly assemble the three output walks. The source region has no repeated support, which earns all three path properties and the precise combined support and edge permutations; the returned walk identities expose the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate.actual_joint_three_path_update`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointRouteSlicing](ActualJointRouteSlicing.md)
