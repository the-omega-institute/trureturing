# Uniqueness of the Padovan Subsequence

## Abstract

Three initial values and a cubic recurrence determine the Padovan subsequence at multiples of three.

**Theorem 1.1 (Uniqueness from three values).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanArithmetic.triple_recurrence_unique`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanArithmetic.triple_recurrence_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A natural-number sequence agreeing with the Padovan numbers at indices three, six, and nine and satisfying b(n+3) + 2b(n+1) = 3b(n+2) + b(n) for positive n equals the Padovan number at index three times n for every positive n.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanArithmetic.triple_recurrence_unique`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](ArcherCyclicDefs.md)
