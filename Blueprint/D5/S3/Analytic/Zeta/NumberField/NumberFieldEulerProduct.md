# Prime-ideal Euler product

## Abstract

Prime-ideal Euler product.

**Definition 1.1 (Nonzero Integral Ideals).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.NonzeroIdeal`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.NonzeroIdeal` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

The subtype of integral ideals of the ring of integers of L that are not the zero ideal.

**Definition 1.2 (Ideal Norm Multiplicity).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.idealNormMultiplicity`

*Formalization.* `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.idealNormMultiplicity` (`✓ std3`).

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

For a natural number n, the number of nonzero integral ideals whose absolute norm equals n.

**Theorem 1.3 (Prime-ideal Euler product).**

Lean statement: `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.dedekindZeta_eq_tprod_primeIdeal`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.dedekindZeta_eq_tprod_primeIdeal` (`✓ std3`). ∎

*Citation.* Chris Birkbeck and the Chebotarev density contributors (2026). *Chebotarev density in Lean*. URL: <https://github.com/CBirkbeck/chebotarev-density/tree/a00054a0e6bbc394b0e81de750db0cd2efc8bd88>.

*Commentary.*

Prime-ideal Euler product (Sharifi, *Algebraic Number Theory*, Theorem 7.1.12, p. 140): for 1 < Re s, ζ_L(s) = ∏_𝔭 (1 - N𝔭^{-s})^{-1} over the nonzero prime ideals of 𝓞 L.

## References

- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.NonzeroIdeal`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.dedekindZeta_eq_tprod_primeIdeal`
- Truth anchor: `D5/S3/Analytic/Zeta/NumberField/NumberFieldEulerProduct.idealNormMultiplicity`
