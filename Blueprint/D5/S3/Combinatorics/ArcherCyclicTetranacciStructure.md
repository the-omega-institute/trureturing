# Structure of Admissible Cycle Words

## Abstract

Joint cycle-form and one-line avoidance bounds the shape of the low arc.

**Theorem 1.1 (First high letter).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.first_high_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.first_high_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

When the high arc is a permutation of a consecutive interval, avoidance of 1324 in the cycle word and 4123 in its successor permutation forces the first high letter to be the smallest in that interval.

**Theorem 1.2 (Length of the low arc).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.low_arc_length_le_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.low_arc_length_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

If the high arc begins with its smallest possible letter and the successor permutation avoids 4123, the increasing low arc after two has length at most two.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.first_high_minimum`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicTetranacciStructure.low_arc_length_le_two`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciCycleWords](ArcherCyclicTetranacciCycleWords.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciPatterns](ArcherCyclicTetranacciPatterns.md)
