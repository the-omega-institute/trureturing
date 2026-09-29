# From Cycle Words to Permutations

## Abstract

A rooted cycle word determines a permutation through its cyclic successors.

**Definition 1.1 (Successor permutation).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.oneLine`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.oneLine` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The one-line permutation of a cycle word records the cyclic successor of each integer from one through the word length.

**Theorem 1.2 (Recovery of a rooted cycle word).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.orbitWord_oneLine`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.orbitWord_oneLine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If a word begins with one and contains every integer from one through its length exactly once, the orbit word of its successor permutation is the original word.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.oneLine`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords.orbitWord_oneLine`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](ArcherCyclicDefs.md)
