# Four-Branch Decomposition

## Abstract

The admissible rooted cycle words decompose into four insertion branches.

**Definition 1.1 (Admissible rooted words).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.words`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.words` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

These words list the integers from one through n, begin with one, avoid 1324 in every rotation, and have successor permutations avoiding 4123.

**Theorem 1.2 (Insertion decomposition).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For n greater than one, a word is admissible exactly when it is obtained by inserting a low arc of length one, two, three, or four into an admissible shorter word.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.decomposition`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition.words`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanDecomposition](ArcherCyclicPadovanDecomposition.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciOneLine](ArcherCyclicTetranacciOneLine.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciStructure](ArcherCyclicTetranacciStructure.md)
