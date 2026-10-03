# Slack Succession

## Abstract

The succession relation for slack continuations gives the Catalan generating series.

**Theorem 1.1 (Slack succession).**

Lean statement: `D5/S3/Combinatorics/LevelSequence/LevelSequenceSuccession.slack_succession`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/LevelSequence/LevelSequenceSuccession.slack_succession` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Toufik Mansour (2026). *Wilf Classes for Level Sequences Avoiding Patterns of Length Three*. DOI: [10.3390/math14111983](https://doi.org/10.3390/math14111983). URL: <https://www.mdpi.com/2227-7390/14/11/1983>.

*Commentary.*

For a nonempty avoiding tail, the slack values of all admissible successors are obtained by the successive cuts determined by the tail and its initial spine.

## References

- Truth anchor: `D5/S3/Combinatorics/LevelSequence/LevelSequenceSuccession.slack_succession`
- Dependency: [D5/S3/Combinatorics/LevelSequence/LevelSequenceSlack](LevelSequenceSlack.md)
- Dependency: [D5/S3/Combinatorics/LevelSequence/LevelSequenceWordCount](LevelSequenceWordCount.md)
