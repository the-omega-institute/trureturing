# Actual Quartic Euler Factors

## Abstract

Actual Quartic Euler Factors

**Theorem 1.1 (Actual unramified residue degree).**

Lean statement: `D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.inertia_degree`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.inertia_degree` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The order of the normalized character value at p is the actual inertia degree of every maximal-order prime above p, for p distinct from r. The cyclotomic stabilizer theorem, surjective restriction to the actual fixed field, and genuine unramifiedness prove this; no splitting pattern is assumed.

**Theorem 1.2 (All actual quartic Euler factors).**

Lean statement: `D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.euler_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.euler_polynomial` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every rational prime p, including two and the ramified conductor r, the product of one minus z to the actual inertia degrees is the product of the four character factors. The ramified factor is one minus z; the other factors follow from actual residue degrees and the number-field fundamental identity.

Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. These author proofs are not independent whole-result acceptance. The signed conductor-4r bridge is established in MercaImaginaryClassNumber and the full sign/MMZ composition in MercaClassNumberCriterion.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.

## References

- Truth anchor: `D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.euler_polynomial`
- Truth anchor: `D5/S3/Arith/CyclotomicFields/MercaQuarticEulerFactors.inertia_degree`
- Dependency: [D5/S3/Arith/CyclotomicFields/MercaQuarticDiscriminant](MercaQuarticDiscriminant.md)
