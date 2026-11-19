# The Actual Relative Ideal Class Number

## Abstract

The Actual Relative Ideal Class Number

**Theorem 1.1 (Convergent relative zeta factorization).**

Lean statement: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.zeta_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.zeta_factorization` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For real part greater than one, the actual quartic Dedekind zeta function is the product of the actual maximal-real Dedekind zeta function and the L-functions of the normalized quartic character and its inverse. Actual local polynomials and convergent HasProd suppliers prove the equality, including ramified primes.

**Theorem 1.2 (Actual Dedekind residue comparison).**

Lean statement: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.residue_relation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.residue_relation` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Take right limits at one in the genuine factorization. Both nonprincipal L-functions are continuous there, and the actual number-field residue formulas identify the limits. This does not choose a quadratic Gauss-sum sign.

**Theorem 1.3 (The one-side class-number product).**

Lean statement: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.LFunction_one_mul_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.LFunction_one_mul_inverse` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For r greater than five the proved CM unit index is one, both actual roots-of-unity groups have order two, and the actual regulator ratio is two. Actual discriminants r cubed and r and the genuine residue formula yield the classical inverse-character L-value product.

**Theorem 1.4 (Norm and genuine relative class number).**

Lean statement: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.relative_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.relative_norm` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The normalized coordinates satisfy k squared plus t squared equals twice the exact quotient of the genuine quartic and real quadratic ideal class numbers. The odd primitive inverse-character functional equation and actual Bernoulli/L-zero identities supply the bridge; the actual real class groups are transported through the proved algebra equivalence.

**Theorem 1.5 (Integrality of the actual quotient).**

Lean statement: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.relative_class_number_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.relative_class_number_integral` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The genuine ideal-class-number quotient is a nonnegative integer, proved from the norm identity and the odd integer coordinates. It is defined as a rational quotient and is never rounded by natural division.

Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. These author proofs are not independent whole-result acceptance. The signed conductor-4r bridge is established in MercaImaginaryClassNumber and the full sign/MMZ composition in MercaClassNumberCriterion.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.LFunction_one_mul_inverse`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.relative_class_number_integral`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.relative_norm`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.residue_relation`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaRelativeClassNumber.zeta_factorization`
- Dependency: [D5/S3/Analytic/Zeta/QuadraticZetaFactorization](QuadraticZetaFactorization.md)
- Dependency: [D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors](../../Arith/CyclotomicFields/MercaQuarticEulerFactors.md)
- Dependency: [D5/S3/Arith/CyclotomicFields/MercaRealEulerFactors](../../Arith/CyclotomicFields/MercaRealEulerFactors.md)
- Dependency: [D5/S3/ArithUnits/MercaQuarticMoments](../../ArithUnits/MercaQuarticMoments.md)
