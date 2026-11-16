# The Positive Quadratic Gauss Sign

## Abstract

The Positive Quadratic Gauss Sign

**Theorem 1.1 (square_sum).**

Lean statement: `D5/S3/Arith/CharacterSums/MercaPositiveGauss.square_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/MercaPositiveGauss.square_sum` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

The actual finite quadratic exponential sum equals the positive real square root. The existing Milgram theorem is applied to the actual rank-one even lattice with Gram matrix (2r), whose discriminant group and phase are identified explicitly.

**Theorem 1.2 (prime_gauss_sum).**

Lean statement: `D5/S3/Arith/CharacterSums/MercaPositiveGauss.prime_gauss_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/MercaPositiveGauss.prime_gauss_sum` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *A class-number criterion for the quartic equality after Theorem 5.5*. URL: <https://oeis.org/A392984>.

*Commentary.*

Root-fiber counting identifies the square exponential sum with the standard Gauss sum of the genuine Legendre character, fixing its positive sign.

Source-owner four-slot audits remain unfinished at https://github.com/the-omega-institute/trureturing/issues/27629. Successful scoped author verification does not replace independent whole-result acceptance.

Historical credit: Haobo Ma and Wenlin Zhang, CC BY 4.0; Joseph S. Farland criterion/sign attribution and OEIS terms; joint Ma-Merca-Zhang application; Louboutin, Hudson and classical class-number/Gauss sources. Existing Yao Xu/catalan-lean4 Apache-2.0 notices are retained. No novelty, priority, consent or publication claim is made.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/MercaPositiveGauss.prime_gauss_sum`
- Truth anchor: `D5/S3/Arith/CharacterSums/MercaPositiveGauss.square_sum`
- Dependency: [D5/S3/Analytic/Zeta/PrimeQuadraticLValues](../../Analytic/Zeta/PrimeQuadraticLValues.md)
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil](../../VertexAlgebra/Characters/LatticeDiscriminantWeil.md)
