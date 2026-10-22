# Sign changes on index occurrences

## Abstract

Even zero-sum sign changes and coordinate permutations preserve even subset spectra.

**Definition 1.1 (Flip an index set).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.flipCoefficients`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/SignAction.flipCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient at i is negated precisely when i belongs to I.

**Theorem 1.2 (Even zero-sum flips).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_zero_flip_preserves_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_zero_flip_preserves_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If I has even cardinality and its original coefficients sum to zero, flipping the coefficients on I preserves the even occurrence spectrum. Symmetric difference with I bijects the even index subsets; the subset-sum identity subtracts the sum over I, which vanishes.

**Theorem 1.3 (Permutation of occurrences).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing by any coordinate permutation preserves the even occurrence spectrum. The induced bijection acts on index subsets, without identifying equal coefficient values.

**Theorem 1.4 (The sign-permutation condition is sufficient).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_of_sign_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_of_sign_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any natural m and arbitrary real families b,c on Fin m, suppose a permutation sigma and an even index set I satisfy sum_I b = 0 and c(sigma i) equals -b(i) on I and b(i) off I. Then their even occurrence spectra coincide. This implication includes zero and repeated coefficients and holds without a parity restriction on m.

**Theorem 1.5 (Odd zero-sum flips exchange parity).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.odd_zero_flip_interchanges_spectra`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.odd_zero_flip_interchanges_spectra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the zero-sum flip set has odd cardinality, symmetric difference carries even index subsets to odd index subsets. The even spectrum after the flip therefore equals the original odd spectrum, with multiplicities preserved.

**Theorem 1.6 (The minimum distinguishes parity).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_ne_odd_of_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_ne_odd_of_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every coefficient is nonzero, the even and odd spectra are unequal. The subset of precisely the negative coefficients is the unique subset attaining the full minimum: equality in the coordinatewise lower bound forces every membership decision. Its sum can occur in only one parity.

**Theorem 1.7 (The obstruction to an odd flip).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.sign_set_even_or_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.sign_set_even_or_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a zero-sum sign flip preserves the even spectrum, either its index set has even cardinality or some original coefficient is zero. An odd flip would identify the even and odd spectra, contradicting the unique minimum when all coefficients are nonzero.

**Theorem 1.8 (Repair flip parity using a zero coordinate).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.repair_flip_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.repair_flip_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any zero-sum flip preserving the even spectrum, there is an even zero-sum flip with the same resulting coefficient family. If the original flip has odd cardinality, the parity obstruction supplies a zero coordinate. Inserting or removing that coordinate changes the flip cardinality by one, while preserving both the coefficient family and the zero sum.

**Definition 1.9 (Negative coefficient indices).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.negativeIndices`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/SignAction.negativeIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The negative indices are precisely the coordinates with strictly negative coefficient.

**Definition 1.10 (Negative mass).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.negativeMass`

*Formalization.* `D5/S3/Combinatorics/SubsetSpectrum/SignAction.negativeMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The negative mass is the sum of the strictly negative coefficients.

**Theorem 1.11 (Signed normalization).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.full_spectrum_signed_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.full_spectrum_signed_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full spectrum is the full spectrum of the absolute coefficients translated by the negative mass. Symmetric difference with the negative index set bijects all index subsets, preserving every occurrence including those caused by zeros.

**Theorem 1.12 (The least full subset sum).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.full_spectrum_minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.full_spectrum_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The negative mass is the least value in the full occurrence spectrum. Every coordinate is minimized by including a negative coefficient and omitting a positive one; zero coefficients may be included or omitted.

**Theorem 1.13 (Reduction to absolute coefficients).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_absolute_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_absolute_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd m at least three, equal even spectra imply equal coefficient totals, equal negative masses, and equal full occurrence spectra of the absolute coefficients. The minimum determines the translation in signed normalization; injectivity of translation then cancels it.

**Theorem 1.14 (Recover the even sign witness from an occurrence matching).**

Lean statement: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_sign_witness_of_absolute_permutation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_sign_witness_of_absolute_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For odd m at least three, let b,c have equal even spectra and let sigma match the absolute values of their coefficient occurrences. Then the same sigma admits an even zero-sum flip set I with c(sigma i) equal to -b(i) on I and b(i) off I. Equal totals force the initial flip sum to vanish; the zero-coordinate construction repairs its parity when necessary.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_ne_odd_of_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_sign_witness_of_absolute_permutation`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_absolute_reduction`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_of_sign_permutation`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_spectrum_permutation`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.even_zero_flip_preserves_spectrum`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.flipCoefficients`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.full_spectrum_minimum`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.full_spectrum_signed_normalization`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.negativeIndices`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.negativeMass`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.odd_zero_flip_interchanges_spectra`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.repair_flip_parity`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/SignAction.sign_set_even_or_zero`
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/EvenBridge](EvenBridge.md)
