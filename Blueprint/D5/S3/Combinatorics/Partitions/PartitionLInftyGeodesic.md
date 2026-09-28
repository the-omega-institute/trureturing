# Endpoint-confined geodesics of partitions

## Abstract

Fixed-mass antitone partition vectors admit shortest coordinate-confined paths in the d-infinity metric, and every unit-step path has at least that many steps.

**Theorem 1.1 (A shortest path between partitions).**

Lean statement: `D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic.partition_lInf_geodesic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic.partition_lInf_geodesic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n and every pair of partitions λ and μ of n, let d∞(λ, μ) be the maximum coordinate difference. There is a path of exactly d∞(λ, μ) adjacent steps through partitions of n. Every coordinate of every vertex lies between the corresponding coordinates of λ and μ. Conversely, any path through partitions of n whose adjacent steps have d∞ at most one has at least d∞(λ, μ) steps.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/PartitionLInftyGeodesic.partition_lInf_geodesic`
