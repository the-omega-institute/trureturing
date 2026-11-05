# CubicThetaOddParity

## Abstract

The actual integral Euler quotient `f3^3/f1`, with its constant-term-one inverse, has an all-index odd dissection: the coefficient at `4*n+1` equals the coefficient at `n`, and the coefficient at `4*n+3` vanishes.

**Theorem 1.1 (core_exponent_mod_four_one).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_exponent_mod_four_one`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_exponent_mod_four_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete integer core exponent is congruent to one modulo four exactly on pairs whose first coordinate is odd and second coordinate is even.

**Theorem 1.2 (core_exponent_mod_four_ne_three).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_exponent_mod_four_ne_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_exponent_mod_four_ne_three` (`✓ std3`). ∎

*Commentary.*

No complete integer core fibre has exponent congruent to three modulo four.

**Definition 1.3 (coreOddEquiv).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv` (`✓ std3`).

*Commentary.*

The affine map `(a,b) ↦ (1-2a,-2b)` is a bijection from the fibre of exponent `n` to the fibre of exponent `4*n+1`; the inverse is proved on the full odd fibre using the mod-four classification.

**Theorem 1.4 (core_product_coeff_mod_four).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_product_coeff_mod_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_product_coeff_mod_four` (`✓ std3`). ∎

*Commentary.*

`CubicThetaCoreProduct.coeff_core_product` turns the affine correspondence and residue-three emptiness into the exact rational coefficients of the existing Euler quotient.

**Definition 1.5 (integralT).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT` (`✓ std3`).

*Commentary.*

`integralT` is defined from the actual integral pentagonal Euler series `f1`, its cubic expansion `f3`, and the constant-term-one inverse of `f1`.

**Theorem 1.6 (integralT_map).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_map`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_map` (`✓ std3`). ∎

*Commentary.*

The integer quotient maps coefficientwise to the exact rational quotient from `CubicThetaCoreProduct`, including a proved compatibility of `PowerSeries.invOfUnit` with the injective map `ℤ → ℚ`.

**Theorem 1.7 (integralT_coeff_mod_four).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four` (`✓ std3`). ∎

*Commentary.*

This is the consumed terminal result for the active implementation: for every natural `n`, `coeff (4*n+1) integralT = coeff n integralT` and `coeff (4*n+3) integralT = 0`. It is a parity sublemma for the whole designated-six-tuple event, not a resolution of that event.

No independent literature-priority, novelty, or whole-problem claim is made.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_map`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.core_product_coeff_mod_four`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaCoreProduct](CubicThetaCoreProduct.md)
