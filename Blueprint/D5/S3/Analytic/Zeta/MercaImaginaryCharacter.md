# The Actual Discriminant Character

## Abstract

The Actual Discriminant Character

**Theorem 1.1 (Literal integer values).**

Lean statement: `D5/S3/Analytic/Zeta/MercaImaginaryCharacter.character_int`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaImaginaryCharacter.character_int` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

At the actual modulus four times r, the character is the product of the lifted character modulo four and the genuine Legendre character. The formula holds on every integer, with zero at nonunits; neither a class number nor a norm table defines its values.

**Theorem 1.2 (Exact conductor and odd quadraticity).**

Lean statement: `D5/S3/Analytic/Zeta/MercaImaginaryCharacter.character_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/MercaImaginaryCharacter.character_properties` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

For every prime r congruent to five modulo eight, the local conductors four and r are coprime. The product conductor is proved to be exactly four r, and the product is quadratic, odd and nonprincipal. These facts supply the imaginary Euler and signed L-value bridges.

Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Author kernel checks and this application exposition do not replace independent whole-result acceptance. The full signed class-number/sign/MMZ composition remains an explicit separate obligation until checked.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices remain intact. No novelty, priority, consent or publication claim is made.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/MercaImaginaryCharacter.character_int`
- Truth anchor: `D5/S3/Analytic/Zeta/MercaImaginaryCharacter.character_properties`
- Dependency: [D5/S3/Analytic/Zeta/PrimeQuadraticLValues](PrimeQuadraticLValues.md)
