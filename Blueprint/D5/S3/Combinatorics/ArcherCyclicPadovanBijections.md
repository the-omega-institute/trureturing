# Insertion Branches for Padovan Words

## Abstract

Insertion branches partition the auxiliary and main classes of rooted avoiders.

**Definition 1.1 (Insert a high block).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.highInsert`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.highInsert` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

This insertion keeps one first, raises the remaining letters above a low block, and appends two followed by the increasing letters from three through m.

**Theorem 1.2 (Split the auxiliary class).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.auxiliary_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.auxiliary_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For k at least two, the auxiliary words are exactly the union of front insertions into good words of size k and final low-block insertions of size two into auxiliary words of index k minus one.

**Theorem 1.3 (Auxiliary cardinality recurrence).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.auxiliary_card_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.auxiliary_card_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For k at least two, the number of auxiliary words of index k is the number of good words of size k plus the number of auxiliary words of index k minus one.

**Theorem 1.4 (Split the main class).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.main_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.main_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For n at least two, the good words of size n are exactly the union of front insertions into good words of size n minus one and high-block insertions into auxiliary words of indices one through n minus two.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.auxiliary_card_recurrence`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.auxiliary_split`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.highInsert`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanBijections.main_split`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanClasses](ArcherCyclicPadovanClasses.md)
