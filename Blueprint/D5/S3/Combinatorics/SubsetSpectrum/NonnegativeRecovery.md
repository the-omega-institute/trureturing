# Nonnegative coefficient recovery

## Abstract

Nonnegative real coefficient multisets are determined by their full subset-sum multisets.

**Theorem 1.1 (Recovery with zeros and repetitions).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.nonnegative_subset_sum_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.nonnegative_subset_sum_recovery` (`✓ std3`). ∎

*Citation.* Andrea Ciprietti, Federico Glaudo (2023). *On The Determination of Sets By Their Subset Sums*. DOI: [10.48550/arXiv.2301.04635](https://doi.org/10.48550/arXiv.2301.04635). URL: <https://arxiv.org/abs/2301.04635v2>.

*Commentary.*

For arbitrary finite multisets s,t of nonnegative reals, equality of their full occurrence spectra implies s=t. The cardinalities need not be assumed equal. Erasing one occurrence of zero from the spectrum removes the empty subset exactly once; its minimum is a least coefficient, including when this coefficient is zero. Cancelling its factor 1+X^a in the natural-coefficient additive monoid algebra reduces the coefficient count. This is a nonnegative consequence of Ciprietti and Glaudo's full-spectrum recovery.

**Theorem 1.2 (Indexed and multiset spectra).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.indexed_full_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.indexed_full_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectrum formed from all subsets of a finite index universe agrees with the multiset powerset construction on the coefficient occurrences. The powerset-map identity preserves repetitions and does not require an injective coefficient map.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.indexed_full_spectrum`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery.nonnegative_subset_sum_recovery`
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/SignAction](SignAction.md)
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/TengokuSubsetSums](TengokuSubsetSums.md)
