# Counting after Omitting a Pair

## Abstract

The two coordinate counts after one pair is removed.

**Theorem 1.1 (The remaining coordinates).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinateCount.card_after_omitting_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinateCount.card_after_omitting_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each subset containing the first distinguished element contains both distinguished elements or belongs to the first side of a pair. A subset omitting it contains neither or belongs to the second side. Removing one distinguished pair subtracts one from each count.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinateCount.card_after_omitting_pair`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitCoordinateCount](UniformCircuitCoordinateCount.md)
