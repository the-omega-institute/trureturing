# Decomposing Padovan Cycle Words

## Abstract

Circular avoidance determines the lower arc and supports recovery of the rooted word.

**Theorem 1.1 (Forced lower arc).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.low_arc_forced`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.low_arc_forced` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If a rooted permutation word has a nonempty block before two and avoids 1324 in every rotation, all letters after two lie below that block, form the consecutive interval beginning at three, and the word formed by one and the first block also avoids 1324 circularly.

**Theorem 1.2 (Recover the high word).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.recover_high_word`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.recover_high_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A circularly 1324-avoiding rooted permutation word with a nonempty block before two is obtained by raising the letters of a shorter circularly avoiding rooted word and appending the consecutive low block.

**Theorem 1.3 (Sufficient lower-arc conditions).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.low_arc_sufficient`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.low_arc_sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A distinct-letter word formed from one, a high block above two, two, and a consecutive lower block avoids 1324 in every rotation when the high block lies above the lower block and the word formed by one and the high block avoids 1324 circularly.

**Theorem 1.4 (Insert two at the front).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.circular_avoidance_insert_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.circular_avoidance_insert_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a distinct-letter word whose letters after one exceed two, placing two immediately after one preserves circular avoidance of 1324 in both directions.

**Theorem 1.5 (Avoidance after high insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.inserted_word_circular_avoid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.inserted_word_circular_avoid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Raising the letters of a rooted permutation word and appending two followed by a consecutive low block preserves circular avoidance of 1324.

**Theorem 1.6 (Recover the front-insertion word).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.recover_front_word`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.recover_front_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A circularly 1324-avoiding rooted permutation word beginning with one and two comes from front insertion into a shorter circularly avoiding rooted permutation word.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.circular_avoidance_insert_two`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.inserted_word_circular_avoid`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.low_arc_forced`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.low_arc_sufficient`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.recover_front_word`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition.recover_high_word`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanBlocks](ArcherCyclicPadovanBlocks.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanPatterns](ArcherCyclicPadovanPatterns.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanRotation](ArcherCyclicPadovanRotation.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanTriples](ArcherCyclicPadovanTriples.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion](ArcherCyclicTetranacciInsertion.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns](ArcherCyclicTetranacciPatterns.md)
