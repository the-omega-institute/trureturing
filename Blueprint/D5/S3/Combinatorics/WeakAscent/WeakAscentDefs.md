# Weak Ascent Sequences and Vincular Avoidance

## Abstract

Weak ascent sequences avoiding 210 and permutations avoiding 2-41-3 define two enumeration problems.

**Definition 1.1 (The weak ascent count).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.wasc`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.wasc` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

The weak ascent count of a sequence is the number of adjacent pairs for which the first entry is at most the second.

**Definition 1.2 (Weak ascent sequences).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.IsWeakAscent`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.IsWeakAscent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

A sequence of nonnegative integers is a weak ascent sequence when its first entry, if present, is zero and each subsequent entry is at most one plus the weak ascent count of the preceding prefix. The empty sequence is included.

**Definition 1.3 (The classical pattern 210).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.Contains210`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.Contains210` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

A sequence contains 210 when three entries at strictly increasing positions are strictly decreasing in value.

**Definition 1.4 (The vincular pattern 2-41-3).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.ContainsV2413`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.ContainsV2413` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

A word contains 2-41-3 when there are positions i, j, j + 1, k in strictly increasing order such that the entry at j + 1 is less than the entry at i, which is less than the entry at k, which is less than the entry at j.

**Definition 1.5 (Weak ascent avoiders of a fixed length).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.weakAvoiders`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.weakAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonnegative n, the set W_n(210) consists of the weak ascent sequences of length n containing no classical pattern 210.

**Definition 1.6 (Vincular avoiders of a fixed size).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.permAvoiders`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.permAvoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonnegative n, the set S_n(2-41-3) consists of the permutations of the integers from one through n containing no vincular pattern 2-41-3.

**Definition 1.7 (The equinumerosity assertion).**

Lean statement: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.claim`

*Formalization.* `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beáta Bényi, Toufik Mansour, José L. Ramírez (2024). *Pattern Avoidance in Weak Ascent Sequences*. DOI: [10.46298/dmtcs.12273](https://doi.org/10.46298/dmtcs.12273). URL: <https://arxiv.org/abs/2309.06518v4>.

*Commentary.*

For every nonnegative n, the number of 210-avoiding weak ascent sequences of length n equals the number of permutations of one through n avoiding 2-41-3.

## References

- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.Contains210`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.ContainsV2413`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.IsWeakAscent`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.permAvoiders`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.wasc`
- Truth anchor: `D5/S3/Combinatorics/WeakAscent/WeakAscentDefs.weakAvoiders`
