# Low-Arc Insertion

## Abstract

Inserting a low arc preserves circular avoidance of 1324.

**Definition 1.1 (Insert a low arc).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.insertWord`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.insertWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Insertion shifts every letter of the old word upward by k, places one first, and appends the increasing letters from two through k.

**Theorem 1.2 (Circular avoidance under insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.circular_1324_insert_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.circular_1324_insert_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a rooted permutation word and positive k, the inserted word contains 1324 in some rotation exactly when the original word does.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.circular_1324_insert_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.insertWord`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](ArcherCyclicDefs.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanRotation](ArcherCyclicPadovanRotation.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns](ArcherCyclicTetranacciPatterns.md)
