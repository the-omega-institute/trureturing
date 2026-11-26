# Normalize a shared distance-three contact

## Abstract

A cube translation and axis permutation preserve the local conditions of shared contacts.

**Theorem 1.1 (Transport to the canonical contact).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactNormalized.exists_normalized_shared_contact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactNormalized.exists_normalized_shared_contact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translate the second endpoint to zero and order the coordinates by the axis permutation. Hamming distances and occupied degrees are preserved. A coordinate flip conjugates to the corresponding flip in the new coordinates, preserving exterior evenness and the exclusion of occupied squares. The normalized vertices and occupied triples match one of the three shared cases.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactNormalized.exists_normalized_shared_contact`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9SharedContactAxisOrbits](Q9SharedContactAxisOrbits.md)
