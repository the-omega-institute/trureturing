# Successors of Padovan Cycle Words

## Abstract

The successor permutation of a split cycle word has an explicit block form.

**Theorem 1.1 (Successors of a split word).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.oneLine_split_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.oneLine_split_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a distinct-letter word beginning with one, followed by a high block, two, and the consecutive low block starting at three, its successor permutation begins with the first high letter and the low block, then one, followed by the successors of the remaining high letters.

**Definition 1.2 (Relabel a successor).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.raiseSuccessor`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.raiseSuccessor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

This map sends one to two, fixes zero, and raises every value at least two by m minus one.

**Theorem 1.3 (Descending pair under relabeling).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.below_descent_map_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.below_descent_map_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A strictly increasing relabeling preserves whether a word has a descending pair whose larger entry lies below a specified threshold.

**Theorem 1.4 (Successors after block insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.oneLine_inserted_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.oneLine_inserted_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Inserting a consecutive low block after a raised high block gives a successor permutation consisting of the raised first high letter, the low successors, one, and the relabeled tail of the old successor permutation.

**Theorem 1.5 (4132 avoidance after insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.inserted_avoid_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.inserted_avoid_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The inserted successor permutation avoids 4132 exactly when the old successor tail avoids 4132 and contains no descent whose larger entry lies below the first high letter.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.below_descent_map_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.inserted_avoid_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.oneLine_inserted_block`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.oneLine_split_block`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor.raiseSuccessor`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanCycleWords](ArcherCyclicPadovanCycleWords.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition](ArcherCyclicPadovanDecomposition.md)
