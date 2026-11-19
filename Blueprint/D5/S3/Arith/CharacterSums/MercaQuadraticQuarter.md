# The Literal Quadratic Quarter Sum

## Abstract

The Literal Quadratic Quarter Sum

**Definition 1.1 (The literal quadratic quarter sum).**

Lean statement: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.quarterSum`

*Formalization.* `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.quarterSum` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The sum uses the actual Legendre character on precisely the positive integers from one through (r-1)/4.

**Definition 1.2 (The literal quarter nonresidue count).**

Lean statement: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.nonresidueCount`

*Formalization.* `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.nonresidueCount` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The count uses the same positive interval and the Legendre value minus one.

**Theorem 1.3 (The length-minus-twice-count identity).**

Lean statement: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.quarter_nonresidue`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.quarter_nonresidue` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Every interval element is a nonzero residue modulo r. The literal quadratic sum is the interval length minus twice the nonresidue count.

**Theorem 1.4 (The signed finite L-zero bridge).**

Lean statement: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.LFunction_zero_quarter`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.LFunction_zero_quarter` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Four exact representative blocks, reflection of the quadratic character, and multiplication by four identify the actual conductor-four-r L-function at zero with twice the literal Legendre quarter sum. No class-number premise occurs.

Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Author kernel checks and this application exposition do not replace independent whole-result acceptance. MercaClassNumberCriterion separately combines these suppliers into the full class-number and sign criterion; independent whole-result acceptance remains pending.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.LFunction_zero_quarter`
- Truth anchor: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.nonresidueCount`
- Truth anchor: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.quarterSum`
- Truth anchor: `D5/S3/Arith/CharacterSums/MercaQuadraticQuarter.quarter_nonresidue`
- Dependency: [D5/S3/Analytic/Zeta/CatalanPrimeOddMoment](../../Analytic/Zeta/CatalanPrimeOddMoment.md)
- Dependency: [D5/S3/Analytic/Zeta/MercaImaginaryCharacter](../../Analytic/Zeta/MercaImaginaryCharacter.md)
