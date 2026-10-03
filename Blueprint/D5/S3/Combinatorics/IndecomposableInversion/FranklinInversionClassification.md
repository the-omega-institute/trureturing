# FranklinInversionClassification

## Abstract

The positions of entries exceeding a later entry determine the star and five-block classification of indecomposable 321- and 1342-avoiders.

**Definition 1.1 (Entries exceeding a later entry).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.Tall`

*Formalization.* `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.Tall` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

A position in a list is tall if there exists a later position within the list whose entry is smaller than the entry at the given position. Positions are numbered from zero.

**Theorem 1.2 (Tall entries are left-to-right maxima).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.tall_ltrMax`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.tall_ltrMax` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

In a list with distinct entries avoiding 321, every tall position within the list is a left-to-right maximum: its entry exceeds every preceding entry.

**Theorem 1.3 (Positions of tall entries).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.tall_block_structure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.tall_block_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

Let p be an indecomposable permutation of one through n, where n is positive, avoiding 321 and 1342, and suppose its first entry is not n. There exist positions r, m and later with one at most r, r at most m, m less than the length of p, and m less than later less than the length of p, such that the entry at m is n and the entry at later is smaller than the first entry. A position within p is tall exactly when it is less than r or equal to m.

**Theorem 1.4 (Classification of indecomposable avoiders).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.classification`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For every nonnegative integer k and every permutation p in I_k(321, 1342), either p is the star permutation with first entry k plus one followed by one through k, or p is a five-block permutation with natural parameters r, t, d and h satisfying r, t and d positive, d at most t, and rt plus d plus h equal to k.

## References

- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.Tall`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.classification`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.tall_block_structure`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification.tall_ltrMax`
- Dependency: [D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionBasic](FranklinInversionBasic.md)
