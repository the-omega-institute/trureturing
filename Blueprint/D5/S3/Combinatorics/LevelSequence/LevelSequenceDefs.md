# Level Sequence Definitions

## Abstract

Definitions for level sequences and avoidance of the patterns 101 and 102.

**Definition 1.1 (Level count).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.lev`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.lev` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

The level of a finite sequence is the number of adjacent equal pairs in the sequence.

**Definition 1.2 (Level sequence predicate).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.IsLevel`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.IsLevel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

A sequence is a level sequence when its first entry is zero and each later entry is at most one plus the level of its preceding prefix.

**Definition 1.3 (Occurrence of 101).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.Contains101`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.Contains101` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

A sequence contains 101 when three positions in increasing order carry values with the first and third equal and the middle smaller.

**Definition 1.4 (Occurrence of 102).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.Contains102`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.Contains102` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

A sequence contains 102 when three positions in increasing order carry values whose first is smaller than the third and whose middle is strictly between them.

**Definition 1.5 (Avoiding level sequences).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.avoiders`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

For a natural number n, the avoiders are the level sequences of length n containing neither 101 nor 102.

**Definition 1.6 (Catalan counting claim).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.claim`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

For every positive n, the cardinality of the avoiders of length n is the Catalan number at index n.

## References

- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.Contains101`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.Contains102`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.IsLevel`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs.lev`
