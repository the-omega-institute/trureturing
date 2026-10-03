# FranklinInversionBasic

## Abstract

Stars and five-block permutations describe the forms of indecomposable permutations avoiding 321 and 1342.

**Definition 1.1 (Star permutation).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.star`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.star` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For a nonnegative integer k, the star permutation is the entry k plus one followed by the increasing list from one through k. At k equal to zero it is the singleton permutation consisting of one.

**Definition 1.2 (Five-block permutation).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.fiveBlock`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.fiveBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For natural numbers r, t, d and h, concatenate the increasing block of r entries starting at t plus one, the increasing block of t minus d entries starting at one, the singleton r plus t plus h plus one, the increasing block of d entries starting at t minus d plus one, and the increasing block of h entries starting at t plus r plus one. Subtraction of natural numbers is truncated at zero.

**Theorem 1.3 (Avoidance and inversions of the five-block family).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.fiveBlock_mem_avoiders`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.fiveBlock_mem_avoiders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For natural numbers r, t, d and h with r, t and d positive and d at most t, the five-block permutation belongs to I_(rt + d + h)(321, 1342). It is a nonempty indecomposable permutation of length r plus t plus h plus one, avoids 321 and 1342, and has rt plus d plus h inversions.

## References

- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.fiveBlock`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.fiveBlock_mem_avoiders`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic.star`
- Dependency: [D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs](FranklinInversionDefs.md)
