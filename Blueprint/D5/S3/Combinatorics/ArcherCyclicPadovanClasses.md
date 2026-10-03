# Rooted Cycle-Word Classes

## Abstract

Two classes of rooted cycle words organize the Padovan enumeration.

**Definition 1.1 (Circularly avoiding words).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.circleWords`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.circleWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

These are permutations of the integers from one through n that begin with one and avoid 1324 in every rotation.

**Definition 1.2 (Good words).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.goodWords`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.goodWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

A good word is a circularly 1324-avoiding rooted word whose successor permutation also avoids 4132.

**Definition 1.3 (Tail condition).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.tailCondition`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.tailCondition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

The tail of the successor permutation avoids 4132 and contains no descent whose larger entry lies below the first letter of the cycle word's tail, with zero used when that tail is empty.

**Definition 1.4 (Auxiliary words).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxWords`

*Formalization.* `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

An auxiliary word of index k is a circularly 1324-avoiding rooted word of length k plus one satisfying the tail condition.

**Theorem 1.5 (End of an auxiliary arc).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_arc_ends_at_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_arc_ends_at_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a distinct-letter word of the form one, h, T, two, R, where R is consecutive from three and all its letters lie below h, the tail condition forces R to be empty.

**Theorem 1.6 (Shape of an auxiliary word).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_word_shape`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_word_shape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Every auxiliary word of positive index either begins with one and two or begins with one, has a nonempty middle block, and ends with two.

**Theorem 1.7 (Tail condition after final insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_last_insert_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_last_insert_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a rooted permutation word with a nonempty tail, raising its tail letters and appending two preserves the tail condition in both directions.

**Theorem 1.8 (Good words under front insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.front_insert_good_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.front_insert_good_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Inserting a new low letter at the front carries a rooted permutation word into the good class exactly when the original word is good.

**Theorem 1.9 (Good words under high insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.high_insert_good_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.high_insert_good_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

For a rooted permutation word and a low block of length at least two, high-block insertion produces a good word exactly when the original word is auxiliary.

**Theorem 1.10 (Auxiliary words under front insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.front_insert_aux_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.front_insert_aux_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Front insertion produces an auxiliary word exactly when the original rooted permutation word is good.

**Theorem 1.11 (Auxiliary words under final insertion).**

Lean statement: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.last_insert_aux_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.last_insert_aux_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kassie Archer, Ethan Borsh, Jensen Bridges, Christina Graves, Millie Jeske (2024). *Pattern-restricted cyclic permutations with a pattern-restricted cycle form*. DOI: [10.48550/arXiv.2408.15000](https://doi.org/10.48550/arXiv.2408.15000). URL: <https://arxiv.org/abs/2408.15000v1>.

*Commentary.*

Raising the tail letters and appending two produces an auxiliary word exactly when the original rooted permutation word is auxiliary.

## References

- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxWords`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_arc_ends_at_two`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_last_insert_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.auxiliary_word_shape`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.circleWords`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.front_insert_aux_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.front_insert_good_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.goodWords`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.high_insert_good_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.last_insert_aux_iff`
- Truth anchor: `D5/S3/Combinatorics/ArcherCyclicPadovanClasses.tailCondition`
- Dependency: [D5/S3/Combinatorics/ArcherCyclicPadovanSuccessor](ArcherCyclicPadovanSuccessor.md)
- Dependency: [D5/S3/Combinatorics/ArcherCyclicTetranacciSuccessor](ArcherCyclicTetranacciSuccessor.md)
