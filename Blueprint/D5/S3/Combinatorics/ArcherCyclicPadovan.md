# Padovan Enumeration of Cyclic Avoiders

## Abstract

The cyclic avoidance numbers for 4132 and 1324 follow a subsequence of the Padovan numbers.

**Theorem 1.1 (The Padovan enumeration).**

$$padovanClaim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovan.result` (`✓ std3`). ∎

*Resolves.* `Problems/archer-cyclic-4132-1324-padovan` (proved) by `D5/S3/Combinatorics/ArcherCyclicPadovan.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"archer-cyclic-4132-1324-padovan","declaration_gid":"D5/S3/Combinatorics/ArcherCyclicPadovan.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For every positive n, the number of cyclic permutations avoiding 4132 in one-line form and 1324 in every cycle form equals the Padovan number at index three times n.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovan.result`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanArithmetic](ArcherCyclicPadovanArithmetic.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanCount](ArcherCyclicPadovanCount.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanCycleWords](ArcherCyclicPadovanCycleWords.md)
