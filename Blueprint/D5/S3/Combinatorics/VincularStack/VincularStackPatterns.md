# Prefix Records and Pattern Obstructions

## Abstract

Prefix records and restriction by value relate input patterns to the stack output.

**Theorem 1.1 (Prefixes with no popped entries).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.no_pop_iff_records`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.no_pop_iff_records` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

Processing a word from an empty stack pops no entries before the final drain precisely when, for every adjacent descent, its lower entry is at most every entry strictly before the upper entry of that descent.

**Theorem 1.2 (Characterizing a separating output gap).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.separating_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.separating_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For a split into a front and a suffix, the corresponding output gap is separating precisely when the front is empty, or the front has no pops before its final drain and the following suffix condition holds. An empty suffix always satisfies the condition. For a suffix starting with e, either the snapshot stack of the front contains an entry less than e, or every suffix entry is less than every front entry.

**Theorem 1.3 (Restriction to bounded values).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.restrict_sc`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.restrict_sc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

For a word of distinct entries and any threshold t, applying SC after deleting all entries greater than t gives the same word as deleting all entries greater than t from the SC output.

**Definition 1.4 (The classical pattern 1324).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.Contains1324`

*Formalization.* `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.Contains1324` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

A word contains 1324 when four entries at strictly increasing positions have the first entry less than the third, the third less than the second, and the second less than the fourth.

**Theorem 1.5 (The obstruction from 1324).**

Lean statement: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.contains1324_not_sortable`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.contains1324_not_sortable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* William Zhao (2024). *Stack-sorting with Stacks Avoiding Vincular Patterns*. DOI: [10.1016/j.disc.2025.114834](https://doi.org/10.1016/j.disc.2025.114834). URL: <https://arxiv.org/abs/2410.17057v1>.

*Commentary.*

If a word of distinct entries contains the classical pattern 1324, its image under SC contains the classical pattern 231.

## References

- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.Contains1324`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.contains1324_not_sortable`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.no_pop_iff_records`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.restrict_sc`
- Truth anchor: `D5/S3/Combinatorics/VincularStack/VincularStackPatterns.separating_gap`
- Dependency: [D5/S3/Combinatorics/VincularStack/VincularStackBasic](VincularStackBasic.md)
