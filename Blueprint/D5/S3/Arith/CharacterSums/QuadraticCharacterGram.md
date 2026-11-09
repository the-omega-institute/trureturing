# QuadraticCharacterGram

## Abstract

The existing conic-counting quadratic-character sum gives shifted correlation. Pairing nonzero residues with their negatives restricts the full correlation to the true lower half. Expanding the two sign choices gives the integral Gram and column-energy identities.

The existing conic-counting quadratic-character sum gives shifted correlation. Pairing nonzero residues with their negatives restricts the full correlation to the true lower half. Expanding the two sign choices gives the integral Gram and column-energy identities.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (correlation).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Correlation of two translates, including the diagonal.

**Theorem 1.2 (sum_even).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_even`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

An even function sums twice over any genuine choice of one element from each nonzero negation pair. All partition hypotheses are explicit and none is a Gram assumption.

**Theorem 1.3 (restricted_gram).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The restricted row Gram identity used for both signs in the Chen-Sun argument. The left side is an actual finite sum; the only geometric input is a half-set partition.

**Theorem 1.4 (restricted_column_energy).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_column_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_column_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Summing the restricted Gram identity gives the integral energy of the column sums. This is the common energy identity for the even and odd prime families.

**Definition 1.5 (primeHalf).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf`

*Formalization.* `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The actual lower half of the nonzero residues, selected by least natural representatives.

**Theorem 1.6 (prime_restricted_gram).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_restricted_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_restricted_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Specialization to the genuine lower-half residue set for every odd prime. No half-set or correlation condition is assumed in this prime statement.

**Theorem 1.7 (sum_primeHalf).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_primeHalf`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_primeHalf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The residue half-set is precisely the positive interval, with its least representatives.

**Theorem 1.8 (primeHalf_card).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf_card`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.CharacterSums.QuadraticCharacterGram.primeHalf_card supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.9 (prime_half_character_cancellation).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_half_character_cancellation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_half_character_cancellation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Pairing the complete zero-sum quadratic character gives cancellation of its half sum.

**Theorem 1.10 (prime_column_energy).**

Lean statement: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_column_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_column_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Actual half-residue column energy for every odd prime. Its hypotheses contain neither an assumed Gram identity nor an assumed norm formula.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.correlation`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.primeHalf_card`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_column_energy`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_half_character_cancellation`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.prime_restricted_gram`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_column_energy`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.restricted_gram`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_even`
- Truth anchor: `D5/S3/Arith/CharacterSums/QuadraticCharacterGram.sum_primeHalf`
- Dependency: [D5/S3/Arith/FiniteFieldQuadraticCharacterSum](../FiniteFieldQuadraticCharacterSum.md)
