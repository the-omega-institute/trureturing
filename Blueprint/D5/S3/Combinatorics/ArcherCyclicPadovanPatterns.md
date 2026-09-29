# Pattern Occurrences in Padovan Words

## Abstract

Order-preserving relabeling and increasing blocks control occurrences of 4132.

**Theorem 1.1 (Increasing relabeling).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_map_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_map_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Applying a strictly increasing map to every letter of a word preserves the occurrence or avoidance of any fixed classical pattern.

**Theorem 1.2 (A high letter followed by one).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_high_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_high_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a word beginning with a value above one and then one, a 4132 occurrence either lies in the remaining suffix or comes from a descending pair there whose larger entry is below the initial value.

**Theorem 1.3 (Increasing middle block).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_increasing_middle_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_increasing_middle_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Prepending an increasing block does not change 4132 occurrence when each later letter is one, two, or exceeds every letter of that block.

**Theorem 1.4 (Descent in the tail).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.descent_tail_in_q`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.descent_tail_in_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Under the stated increasing-middle and size conditions, a 213 triple in the middle block followed by one and a tail has its descending pair entirely in the tail.

**Theorem 1.5 (Remove the middle block).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_high_middle_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_high_middle_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

With an initial high letter, an increasing middle block, one, and a suitably separated suffix, removing the middle block preserves whether the word contains 4132.

**Definition 1.6 (Raise high letters).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.raiseHigh`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.raiseHigh` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The map fixes zero and one and raises every letter at least two by m minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_high_middle_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_high_one_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_4132_increasing_middle_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.contains_map_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.descent_tail_in_q`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.raiseHigh`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicDefs](ArcherCyclicDefs.md)
