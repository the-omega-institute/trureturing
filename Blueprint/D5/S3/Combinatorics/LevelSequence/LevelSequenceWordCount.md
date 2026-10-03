# Word Counts by Alphabet Size

## Abstract

Bounded avoiding words satisfy a first-letter convolution recurrence.

**Definition 1.1 (Bounded avoiding words).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.words`

*Formalization.* `D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.words` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

For alphabet size a and word length n, the word set consists of length-n words with entries below a that avoid 101 and 102.

**Theorem 1.2 (Alphabet recurrence).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.alphabet_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.alphabet_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

The count of bounded avoiding words of length n plus one is the sum over the first letter and the cut position of the product of the two corresponding smaller word counts.

## References

- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.alphabet_recurrence`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount.words`
- Dependency: [D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent](LevelSequenceDescent.md)
