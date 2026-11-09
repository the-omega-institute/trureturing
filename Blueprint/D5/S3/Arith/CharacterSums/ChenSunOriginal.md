# ChenSunOriginal

## Abstract

The four branches of Chen-Sun Conjecture1.1(1.11) hold for every prime p>3. In order p=1,5,3,7 modulo8 the residues are 4*(1-(-1)^((p-1)/8)), -2, p+1-(-1)^((h-1)/2)*h, and 2-(-1)^((h-1)/2)*h modulo16. Here h is literally NumberField.classNumber of the proved imaginary quadratic field with its true maximal order. The finite congruences, actual class-number square and odd-h sign identity supply all hypotheses; the fallback zero in originalResidue is proved unreachable. No finite prime cutoff is present. Draft delivery still requires independent formal source review and CI; novelty, priority, official acceptance and unique credit are separate unproved claims.

The four branches of Chen-Sun Conjecture1.1(1.11) hold for every prime p>3. In order p=1,5,3,7 modulo8 the residues are 4*(1-(-1)^((p-1)/8)), -2, p+1-(-1)^((h-1)/2)*h, and 2-(-1)^((h-1)/2)*h modulo16. Here h is literally NumberField.classNumber of the proved imaginary quadratic field with its true maximal order. The finite congruences, actual class-number square and odd-h sign identity supply all hypotheses; the fallback zero in originalResidue is proved unreachable. No finite prime cutoff is present. Draft delivery still requires independent formal source review and CI; novelty, priority, official acceptance and unique credit are separate unproved claims.

Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.

**Theorem 1.1 (mod_eight_five).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_five`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The p=5 mod8 branch of the original inclusive double sum.

**Theorem 1.2 (mod_eight_one).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The p=1 mod8 branch, with the literal natural exponent (p-1)/8.

**Definition 1.3 (imaginaryClassNumber).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.imaginaryClassNumber`

*Formalization.* `D5/S3/Arith/CharacterSums/ChenSunOriginal.imaginaryClassNumber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Here h is exactly the cardinality of the ideal class group of the ring of integers of the proved quadratic number field, not a character-sum definition.

**Theorem 1.4 (mod_eight_three).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The p=3 mod8 branch uses the proved actual-class-number square and oddness.

**Theorem 1.5 (mod_eight_seven).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The p=7 mod8 branch, with the same actual maximal-order class number.

**Definition 1.6 (originalResidue).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.originalResidue`

*Formalization.* `D5/S3/Arith/CharacterSums/ChenSunOriginal.originalResidue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

The four original residues. The final zero case is unreachable for primes p>3. The class-number branches instantiate the proved field only when p=3 mod4.

**Theorem 1.7 (full_original).**

Lean statement: `D5/S3/Arith/CharacterSums/ChenSunOriginal.full_original`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/ChenSunOriginal.full_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Deyi Chen and Zhi-Wei Sun (2024). *On determinants involving (j+k/p) plus or minus (j-k/p)*. DOI: [10.48550/arXiv.2409.08213](https://doi.org/10.48550/arXiv.2409.08213). URL: <https://arxiv.org/html/2409.08213v4#S1.E11>.

*Commentary.*

Chen-Sun arXiv:2409.08213v4 Conjecture 1.1(1.11), all primes p>3. The double sum is literal (1.8); h in the two odd branches is NumberField.classNumber of the maximal order of Q(sqrt(-p)), identified by PrimeImaginary.sqrtFieldEquiv and PrimeImaginary.maximalOrderEquiv.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.full_original`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.imaginaryClassNumber`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_five`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_one`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_seven`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.mod_eight_three`
- Truth anchor: `D5/S3/Arith/CharacterSums/ChenSunOriginal.originalResidue`
- Dependency: [D5/S3/Analytic/Zeta/QuadraticClassNumberSquare](../../Analytic/Zeta/QuadraticClassNumberSquare.md)
- Dependency: [D5/S3/Arith/CharacterSums/ChenSunModSixteen](ChenSunModSixteen.md)
