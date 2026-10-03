# FranklinInversionDefs

## Abstract

Indecomposable permutations avoiding 321 and 1342 are grouped by their number of inversions.

**Definition 1.1 (Number of inversions).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.inv`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.inv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For a list of natural numbers, the inversion number is the number of pairs of positions i and j such that i is less than j and the entry at i is greater than the entry at j. Positions are numbered from zero and both positions are less than the length of the list.

**Definition 1.2 (Indecomposability).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.Indecomposable`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.Indecomposable` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

A list is indecomposable if, for every positive i strictly less than its length, its prefix of length i is not a permutation of one through i. For a permutation, this excludes a decomposition as the direct sum of two nonempty permutations.

**Definition 1.3 (Indecomposable avoiders with a fixed inversion number).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.avoiders`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.avoiders` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For a nonnegative integer k, I_k(321, 1342) consists of all nonempty permutations of one through n, with n allowed to vary, that are indecomposable, have exactly k inversions and avoid the classical patterns 321 and 1342.

**Definition 1.4 (The conjectured count).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.claim`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

The conjecture states that, for every nonnegative integer k, the number of permutations in I_k(321, 1342) equals k(k + 1)/2 + 1.

## References

- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.Indecomposable`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.avoiders`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionDefs.inv`
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingDefs](../Nonnesting/NonnestingDefs.md)
