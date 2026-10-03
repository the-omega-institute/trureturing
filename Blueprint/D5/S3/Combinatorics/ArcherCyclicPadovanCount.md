# Padovan Counting Recurrence

## Abstract

The good-word counts satisfy a recurrence involving the auxiliary classes.

**Theorem 1.1 (Good-word cardinality recurrence).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanCount.main_card_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanCount.main_card_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For n at least two, the number of good words of size n equals the number of good words of size n minus one plus the sum of auxiliary-word counts over indices one through n minus two.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanCount.main_card_recurrence`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanBijections](ArcherCyclicPadovanBijections.md)
