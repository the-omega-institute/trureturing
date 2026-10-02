# A Pattern Characterization of the Sorting Class

## Abstract

The sorting class is characterized by avoidance of 1324 and a shaded 2413 pattern.

**Definition 1.1 (The shaded 2413 pattern).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.ContainsMesh2413`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.ContainsMesh2413` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A word contains the shaded 2413 pattern when positions a, b, c, d are strictly increasing, their values satisfy w(c) less than w(a) less than w(d) less than w(b), every entry before b is at least w(a), and no entry strictly between b and c has value strictly between w(a) and w(b).

**Theorem 1.2 (An obstruction created by a maximum).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.maximum_insertion_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.maximum_insertion_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Let a word have distinct entries and an SC output avoiding 231. If inserting an entry greater than every original entry makes its SC output contain 231, the new word contains either 1324 or the shaded 2413 pattern.

**Theorem 1.3 (Patterns in every nonsortable word).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.non_sortable_has_pattern`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.non_sortable_has_pattern` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

If a word of distinct entries has an SC output containing 231, the input word contains either the classical pattern 1324 or the shaded 2413 pattern.

**Theorem 1.4 (The avoidance characterization).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.sortable_iff_avoids1324_and_mesh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.sortable_iff_avoids1324_and_mesh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For every word of distinct entries, its image under SC avoids 231 if and only if the word avoids both the classical pattern 1324 and the shaded 2413 pattern.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.ContainsMesh2413`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.maximum_insertion_obstruction`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.non_sortable_has_pattern`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.sortable_iff_avoids1324_and_mesh`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackPatterns](VincularStackPatterns.md)
