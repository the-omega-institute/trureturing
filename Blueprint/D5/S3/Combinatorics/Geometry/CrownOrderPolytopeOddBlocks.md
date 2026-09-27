# Geometry of odd crown blocks

## Abstract

Parity imbalance determines extremality of each odd block.

The parity-majority orientation is the odd-block argument in the proof of source Lemma 3.2 and the endpoint selection in Proposition 3.3.

**Theorem 1.1 (Odd blocks have a unique parity majority).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks.crownOddBlock_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks.crownOddBlock_geometry` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two, every odd block of a connected cycle partition has even-vertex and odd-vertex counts differing by one. An even majority excludes incoming crown edges from other blocks; an odd majority excludes outgoing edges to other blocks. These orientations are conclusions derived from the actual block geometry.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks.crownOddBlock_geometry`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions](CrownOrderPolytopeCyclePartitions.md)
