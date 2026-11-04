# ChenSunModSixteen

## Abstract

The common factorial product fixes the odd central half-sum parity and the even correction parity. Substitution in the exact energies yields d=-2m^2 modulo16 for every prime p=4m+1 and 2d=c^2+4m^2-3 modulo32 for every prime p=4m+3. The modulus32 is retained until the final factor-two cancellation.

The common factorial product fixes the odd central half-sum parity and the even correction parity. Substitution in the exact energies yields d=-2m^2 modulo16 for every prime p=4m+1 and 2d=c^2+4m^2-3 modulo32 for every prime p=4m+3. The modulus32 is retained until the final factor-two cancellation.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (odd_half_sum_parity).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_half_sum_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_half_sum_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The factorial-product parity of the odd-case central quotient sum.

**Theorem 1.2 (even_half_sum_parity).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_half_sum_parity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_half_sum_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The same factorial product also fixes the even-case correction parity.

**Theorem 1.3 (odd_doubleSum_mod32).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_doubleSum_mod32`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_doubleSum_mod32` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The class-number-free odd-prime-family congruence retains the factor two, which is essential for subsequently cancelling the modulus from 32 to 16.

**Theorem 1.4 (even_doubleSum_mod16).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_doubleSum_mod16`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_doubleSum_mod16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The even-prime-family congruence includes every p congruent to one modulo four.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_doubleSum_mod16`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.even_half_sum_parity`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_doubleSum_mod32`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunModSixteen.odd_half_sum_parity`
- Dependency: [D5/S3/Arith/CharacterSums/ChenSunDoubleCharacter](ChenSunDoubleCharacter.md)
- Dependency: [D5/S3/Arith/CharacterSums/QuadraticPrefixParity](QuadraticPrefixParity.md)
