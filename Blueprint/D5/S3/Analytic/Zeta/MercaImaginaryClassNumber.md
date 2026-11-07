# The Signed Actual Imaginary Class Number

## Abstract

The Signed Actual Imaginary Class Number

**Theorem 1.1 (Actual imaginary zeta factorization).**

Lean statement: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.zeta_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.zeta_factorization` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Every rational-prime Euler factor, including both ramified primes, gives the factorization of the Dedekind zeta function of the actual maximal order for real part greater than one.

**Theorem 1.2 (The actual class-number value at one).**

Lean statement: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.LFunction_one`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.LFunction_one` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The actual field residue, maximal-order regulator one and torsion order two give pi times its genuine ideal class number divided by twice the positive square root of r.

**Theorem 1.3 (The signed class-number value at zero).**

Lean statement: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.LFunction_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.LFunction_zero` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The positive Gauss sign and the primitive odd quadratic functional equation give L(0,eta) equal to the genuine NumberField.classNumber, retaining the sign.

**Theorem 1.4 (The exact class-number half).**

Lean statement: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.class_number_quarter`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.class_number_quarter` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The genuine ideal class number is twice the literal Legendre quarter sum. Its integer half is exact, with evenness proved before any sign interpretation.

Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Author kernel checks and this application exposition do not replace independent whole-result acceptance. MercaClassNumberCriterion separately combines these suppliers into the full class-number and sign criterion; independent whole-result acceptance remains pending.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.LFunction_one`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.LFunction_zero`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.class_number_quarter`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaImaginaryClassNumber.zeta_factorization`
- Dependency: [D5/S3/Analytic/Zeta/QuadraticZetaFactorization](QuadraticZetaFactorization.md)
- Dependency: [D5/S3/Arith/CharacterSums/MercaImaginaryGauss](../../Arith/CharacterSums/MercaImaginaryGauss.md)
- Dependency: [D5/S3/Arith/CharacterSums/MercaQuadraticQuarter](../../Arith/CharacterSums/MercaQuadraticQuarter.md)
- Dependency: [D5/S3/Arith/QuadraticFields/MercaImaginaryEulerFactors](../../Arith/QuadraticFields/MercaImaginaryEulerFactors.md)
