# Descent Criteria for Pattern Avoidance

## Abstract

Descent criteria characterize avoidance of 101 and 102.

**Theorem 1.1 (Strong descent criterion).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.strong_descent`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.strong_descent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

A word avoids 101 and 102 exactly when every descent from an earlier entry to a later smaller entry remains strictly below that earlier entry at all subsequent positions.

**Theorem 1.2 (Append criterion).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.append_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.append_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

For a nonempty word, appending a letter preserves avoidance of 101 and 102 exactly when the new letter is smaller than every earlier entry that can be the first entry of a forbidden descent pattern.

## References

- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.append_criterion`
- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceDescent.strong_descent`
- Dependency: [D5/S3/Combinatorics/LevelSequence/LevelSequenceDefs](LevelSequenceDefs.md)
