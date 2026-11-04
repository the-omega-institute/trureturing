# ChenSunDoubleCharacter

## Abstract

The defining double sum uses both inclusive natural intervals and the integer symbol of j squared plus j times k. Multiplicativity and reflected prefixes reduce it to a triangle. The genuine restricted Gram norms give exact even and odd energy identities, before any modular or class-number substitution.

The defining double sum uses both inclusive natural intervals and the integer symbol of j squared plus j times k. Multiplicativity and reflected prefixes reduce it to a triangle. The genuine restricted Gram norms give exact even and odd energy identities, before any modular or class-number substitution.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Definition 1.1 (doubleSum).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum`

*Formalization.* `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Literal equation (1.8) of Chen-Sun arXiv:2409.08213v4; both endpoints are inclusive.

**Theorem 1.2 (doubleSum_eq_row_sum).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum_eq_row_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum_eq_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Multiplicativity changes each summand into the row form used by the Gram identity.

**Theorem 1.3 (twice_doubleSum_triangle).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.twice_doubleSum_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.twice_doubleSum_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Unconditional integral triangular identity for every odd prime; no class-number input.

**Definition 1.4 (columnSum).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum`

*Formalization.* `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Actual column sums of the two restricted character matrices, with integer arguments.

**Theorem 1.5 (columnSum_eq_prefix).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum_eq_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum_eq_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The exact Lean declaration D5.S3.Arith.CharacterSums.ChenSunDoubleCharacter.columnSum_eq_prefix supplies this step in the proof chain described above; its complete Lean statement is retained in the scoped report. The pinned projection corpus has no formula for this new declaration.

**Theorem 1.6 (column_energy).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.column_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.column_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Restricted Gram energy transported to the literal natural interval.

**Theorem 1.7 (even_columnSum).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_columnSum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_columnSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The even-case column vector is a+4b, with b an actual integral partialSum quotient.

**Theorem 1.8 (odd_columnSum).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_columnSum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_columnSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The odd-case column vector is -a+4b, with the zero midpoint included.

**Theorem 1.9 (even_energy_exact).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_energy_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_energy_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Exact even-case energy identity. The remaining mod-sixteen step is factorial parity.

**Theorem 1.10 (odd_energy_exact).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_energy_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_energy_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Exact odd-case energy identity, before reflection and factorial parity reduce it modulo 32.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.columnSum_eq_prefix`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.column_energy`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.doubleSum_eq_row_sum`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_columnSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.even_energy_exact`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_columnSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.odd_energy_exact`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter.twice_doubleSum_triangle`
- Dependency: [D5/S3/Arith/CharacterSums/QuadraticCharacterGram](QuadraticCharacterGram.md)
- Dependency: [D5/S3/Arith/CharacterSums/QuadraticPrefixEnergy](QuadraticPrefixEnergy.md)
- Dependency: [D5/S3/Arith/CharacterSums/QuadraticSignProducts](QuadraticSignProducts.md)
