# An ascent in the second inflated block

## Abstract

Inflating the second entry of a simple permutation of size at least four by a permutation block containing 12 produces an occurrence of 2341, provided that second entry is not the minimum.

**Definition 1.1 (Inflating an entry).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackInflation.inflate`

*Formalization.* `D5/S3/Combinatorics/PopStack/PopStackInflation.inflate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

To inflate the entry of p at position i by a block b, replace that entry v by the entries of b, each first increased by v and then decreased by one. For every other entry greater than v, first add the length of b and then subtract one. The prefix before i and the suffix after i retain their order. Positions are numbered from zero, and an absent entry has value zero; subtraction is truncated at zero.

**Theorem 1.2 (An ascent in the first inflated block).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackInflation.ascending_first_inflation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackInflation.ascending_first_inflation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Inflating the first entry of a simple permutation of size at least three by a permutation block containing 12 produces an occurrence of 2341.

**Theorem 1.3 (An ascent in the second inflated block).**

Lean statement: `D5/S3/Combinatorics/PopStack/PopStackInflation.ascending_second_inflation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PopStack/PopStackInflation.ascending_second_inflation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Lapo Cioni, Luca Ferrari, Rebecca Smith (2025). *Sorting permutations using a pop stack with a bypass*. DOI: [10.1016/j.disc.2025.114964](https://doi.org/10.1016/j.disc.2025.114964). URL: <https://arxiv.org/abs/2503.08285v1>.

*Commentary.*

Inflating the second entry of a simple permutation of size at least four by a permutation block containing 12 produces an occurrence of 2341, provided that second entry is not the minimum.

## References

- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackInflation.ascending_first_inflation`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackInflation.ascending_second_inflation`
- Truth anchor: `D5/S3/Combinatorics/PopStack/PopStackInflation.inflate`
- Dependency: [D5/S3/Combinatorics/PopStack/PopStackDefs](PopStackDefs.md)
