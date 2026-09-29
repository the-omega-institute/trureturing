# Rotations and Circular Subwords

## Abstract

Pattern occurrences in circular subwords can be transferred between rotations.

**Theorem 1.1 (Rotate a subword).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.rotate_sublist_of_sublist`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.rotate_sublist_of_sublist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Every rotation of a subsequence of a word is a subsequence of some rotation of the full word.

**Theorem 1.2 (Root a circular quadruple).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.rotate_quadruple_to_first`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.rotate_quadruple_to_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If four letters occur in order in some rotation, another rotation begins with the first of those letters and has the other three as a subsequence of its tail.

**Theorem 1.3 (Circular avoidance of subwords).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.circular_avoidance_sublist`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.circular_avoidance_sublist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Every subsequence of a word that avoids a fixed pattern in all rotations also avoids that pattern in all of its own rotations.

**Theorem 1.4 (Root a 1324 occurrence).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.circular_1324_iff_minimum_rooted`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.circular_1324_iff_minimum_rooted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A circular word contains 1324 in some rotation exactly when some rotation begins with a letter a and has a subsequence c, b, d in its tail with a less than b less than c less than d.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.circular_1324_iff_minimum_rooted`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.circular_avoidance_sublist`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.rotate_quadruple_to_first`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanRotation.rotate_sublist_of_sublist`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](ArcherCyclicDefs.md)
