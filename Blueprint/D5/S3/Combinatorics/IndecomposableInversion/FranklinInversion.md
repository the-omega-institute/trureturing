# FranklinInversion

## Abstract

The number of indecomposable 321- and 1342-avoiders with k inversions is k(k - 1)/2 + 1, refuting the conjectured count k(k + 1)/2 + 1.

**Theorem 1.1 (The corrected count).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.avoiders_ncard`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.avoiders_ncard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

For every nonnegative integer k, the number of indecomposable permutations with exactly k inversions avoiding 321 and 1342 is k(k - 1)/2 + 1. At k equal to zero the count is one; subtraction of natural numbers is truncated at zero.

**Theorem 1.2 (Refutation of the conjectured count).**

Lean statement: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atli Fannar Franklín (2024). *Pattern avoiding permutations enumerated by inversions*. DOI: [10.48550/arXiv.2410.07467](https://doi.org/10.48550/arXiv.2410.07467). URL: <https://arxiv.org/abs/2410.07467v4>.

*Commentary.*

The conjecture that I_k(321, 1342) has k(k + 1)/2 + 1 elements for every nonnegative integer k is false. At k equal to one, the corrected count is one, whereas the conjectured formula gives two.

## References

- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.avoiders_ncard`
- Truth anchor: `D5/S3/Combinatorics/IndecomposableInversion/FranklinInversion.result`
- Dependency: [D5/S3/Combinatorics/IndecomposableInversion/FranklinInversionClassification](FranklinInversionClassification.md)
