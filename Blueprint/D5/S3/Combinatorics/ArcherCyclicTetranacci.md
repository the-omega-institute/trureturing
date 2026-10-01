# Tetranacci Enumeration of Cyclic Avoiders

## Abstract

The cyclic avoidance numbers for 4123 and 1324 follow the Tetranacci sequence.

**Theorem 1.1 (The Tetranacci enumeration).**

$$tetranacciClaim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacci.result` (`✓ std3`). ∎

*Resolves.* `Problems/archer-cyclic-4123-1324-tetranacci` (proved) by `D5/S3/Combinatorics/ArcherCyclicTetranacci.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"archer-cyclic-4123-1324-tetranacci","declaration_gid":"D5/S3/Combinatorics/ArcherCyclicTetranacci.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For every positive n, the number of cyclic permutations avoiding 4123 in one-line form and 1324 in every cycle form equals the Tetranacci number at index n plus two.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacci.result`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanCycleWords](ArcherCyclicPadovanCycleWords.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciDecomposition](ArcherCyclicTetranacciDecomposition.md)
