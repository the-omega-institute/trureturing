# Actual Route Inventories

## Abstract

Map the same cycle, pieces and cuts through an injective graph homomorphism.

**Theorem 1.1 (Transport an Actual Cycle Partition).**

Lean statement: `D5/S3/Combinatorics/Graph/Walks/ActualPartitionTransport.actual_cycle_partition_map`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/ActualPartitionTransport.actual_cycle_partition_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective graph homomorphism maps the supplied cycle, every actual piece and every removed cut together. The same mapped cycle remains a cycle; all mapped pieces are simple paths, their supports permute its support tail, their edges permute its exact filtered edge list, and every mapped cut belongs to it. No replacement partition certificate is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/ActualPartitionTransport.actual_cycle_partition_map`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing](EdgeSlicing.md)
