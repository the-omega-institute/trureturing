# Triples in Separated Blocks

## Abstract

Separated increasing low blocks cannot contribute letters to certain 213 triples.

**Theorem 1.1 (Triple before a low block).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanTriples.triple_213_in_high`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanTriples.triple_213_in_high` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If every high-block letter exceeds every letter of an increasing low block, any subsequence c, b, d with b less than c less than d lies entirely in the high block.

**Theorem 1.2 (Triple after a low block).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanTriples.triple_213_after_low`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanTriples.triple_213_after_low` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If an increasing low block precedes a block of larger letters, any subsequence c, b, d with b less than c lies entirely in the later high block.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanTriples.triple_213_after_low`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanTriples.triple_213_in_high`
