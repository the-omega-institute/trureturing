# An Exhaustive Actual Joint Partition Update

## Abstract

Recombined actual paths exhaust the supplied Hamilton cycle and retain exactly its uncut edges.

The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.

**Theorem 1.1 (Recover the Whole New Actual Partition).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate.actual_joint_partition_of_cycle_inventory`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate.actual_joint_partition_of_cycle_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full support and edge inventories of one supplied Hamilton cycle include the actual P tail, route, connector, retained a edge and old deleted marks. Recombine the three actual paths and keep every other supplied piece. The result covers every vertex once, retains exactly the filtered cycle edges and has a number of pieces equal to cut cardinality. Source-cycle simplicity proves cut distinctness and prevents deleted supplier edges from being reintroduced.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate.actual_joint_partition_of_cycle_inventory`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate](ActualJointThreePathUpdate.md)
