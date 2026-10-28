# Even and full subset spectra

## Abstract

The first moment and complementation recover the full spectrum from its even part in odd length.

**Definition 1.1 (Even index subsets).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.evenSubsets`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.evenSubsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index set s, evenSubsets s consists of its subsets with even cardinality.

**Definition 1.2 (Odd index subsets).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.oddSubsets`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.oddSubsets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite index set s, oddSubsets s consists of its subsets with odd cardinality.

**Definition 1.3 (The even occurrence spectrum).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.evenSubsetSums`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.evenSubsetSums` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For b indexed by s, each even index subset contributes one occurrence of its coefficient sum. Equal numerical sums from different subsets remain separate occurrences; zero coefficients and repeated coefficients are allowed.

**Definition 1.4 (The odd occurrence spectrum).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.oddSubsetSums`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.oddSubsetSums` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each odd index subset contributes one occurrence of its coefficient sum.

**Definition 1.5 (The full occurrence spectrum).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.fullSubsetSums`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.fullSubsetSums` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each index subset, including the empty set exactly once, contributes one occurrence of its sum.

**Theorem 1.6 (The even incidence first moment).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.even_first_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.even_first_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If s has at least two indices, summing the even spectrum gives 2^(|s|-2) times the sum of the coefficients. Inserting one index splits subsets into those containing it and those avoiding it, interchanges the two parities in the containing part, and gives the cardinal and weighted recurrences.

**Theorem 1.7 (Complementation reflects the even spectrum).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.odd_spectrum_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.odd_spectrum_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an odd finite index universe and total coefficient sum B, the odd spectrum is the multiset image of the even spectrum under x ↦ B-x. Complementation is a bijection on index subsets, so this equality preserves multiplicities even when several subsets have the same sum.

**Theorem 1.8 (Even equality determines full equality).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.even_spectrum_determines_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.even_spectrum_determines_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m be odd and at least three, and let b,c be arbitrary real coefficient families on Fin m. Equality of their even occurrence spectra implies equality of their total coefficient sums and equality of their full occurrence spectra. The positive first-moment factor determines the common total; reflection then recovers both odd spectra, and adjoining the even and odd parts recovers the full spectra.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.evenSubsetSums`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.evenSubsets`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.even_first_moment`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.even_spectrum_determines_full`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.fullSubsetSums`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.oddSubsetSums`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.oddSubsets`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/EvenBridge.odd_spectrum_reflection`
