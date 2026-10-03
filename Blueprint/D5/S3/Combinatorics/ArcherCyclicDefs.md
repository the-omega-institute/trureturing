# Cyclic Pattern Avoidance

## Abstract

Cyclic pattern avoiders and the two counting sequences are defined.

**Definition 1.1 (Image of a permutation).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.image`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.image` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The image of x is the list entry at zero-based index x minus one, with zero used when that index is beyond the list.

**Definition 1.2 (Orbit word).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.orbitWord`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.orbitWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The orbit word lists the first n iterates of one under a permutation of length n.

**Definition 1.3 (Single-cycle condition).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.IsCyclic`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.IsCyclic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A permutation is cyclic when its orbit word contains each integer from one through its length exactly once.

**Definition 1.4 (Cyclic avoiders).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.cyclicAvoiders`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.cyclicAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

This set consists of cyclic permutations of n letters whose one-line form avoids the first pattern and whose every rotated cycle word avoids the second pattern.

**Definition 1.5 (Tetranacci sequence).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.tetranacci`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.tetranacci` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The sequence begins 0, 0, 0, 1, and each later term is the sum of the previous four terms.

**Definition 1.6 (Padovan sequence).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.padovan`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.padovan` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The sequence begins 1, 0, 0, and each term from index three onward is the sum of the terms two and three positions earlier.

**Definition 1.7 (Tetranacci count).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.tetranacciClaim`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.tetranacciClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For every positive n, the number of cyclic permutations avoiding 4123 in one-line form and 1324 in every cycle form equals the Tetranacci number at index n plus two.

**Definition 1.8 (Padovan count).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicDefs.padovanClaim`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicDefs.padovanClaim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For every positive n, the number of cyclic permutations avoiding 4132 in one-line form and 1324 in every cycle form equals the Padovan number at index three times n.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.IsCyclic`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.cyclicAvoiders`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.image`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.orbitWord`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.padovan`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.padovanClaim`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.tetranacci`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicDefs.tetranacciClaim`
- Dependency: [D5/S3/Combinatorics/ArrowWilfDefs](ArrowWilfDefs.md)
