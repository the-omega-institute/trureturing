# Successors After Low-Arc Insertion

## Abstract

The successor permutation of an inserted word has an explicit low prefix and relabeled suffix.

**Definition 1.1 (Relabel old successors).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.relabel`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

This map fixes zero, sends one to one when k is one and to two otherwise, and shifts every larger value upward by k.

**Definition 1.2 (Low successor prefix).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.lowPrefix`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.lowPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The low prefix is two when k is one; otherwise it begins with k plus one, continues from three through k, and ends with one.

**Theorem 1.3 (Successor permutation after insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.oneLine_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.oneLine_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a rooted permutation word and positive k, the successor permutation of its inserted word is the low prefix followed by the original successor permutation with its entries relabeled.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.lowPrefix`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.oneLine_insert`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor.relabel`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords](ArcherCyclicTetranacciCycleWords.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion](ArcherCyclicTetranacciInsertion.md)
