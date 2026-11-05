# CubicThetaOddParity

## Abstract

The actual integral Euler quotient `f3^3/f1`, with its constant-term-one inverse, has an all-index odd dissection: the coefficient at `4*n+1` equals the coefficient at `n`, and the coefficient at `4*n+3` vanishes.

**Definition 1.1 (coreOddEquiv).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The affine map `(a,b) ↦ (1-2a,-2b)` is a bijection from the complete core fibre of exponent `n` to the complete core fibre of exponent `4*n+1`. Private consumed lemmas classify the two coordinate parities on the odd fibre and exclude exponent `4*n+3`.

**Definition 1.2 (integralT).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT`

*Formalization.* `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT` (`✓ std3`).

*Commentary.*

`integralT` is defined from the actual integral pentagonal Euler series `f1`, its cubic expansion `f3`, and the constant-term-one inverse of `f1`.

**Theorem 1.3 (integralT_coeff_mod_four).**

Lean statement: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural `n`, `coeff (4*n+1) integralT = coeff n integralT` and `coeff (4*n+3) integralT = 0`. The proof consumes `CubicThetaCoreProduct.coeff_core_product` after the new lattice correspondence, and it proves the `ℤ → ℚ` unit-inverse compatibility before using injectivity. This is a parity sublemma for the active designated-six-tuple event, not a resolution of that event.

No independent literature-priority, novelty, or whole-problem claim is made.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.integralT_coeff_mod_four`
- Truth anchor: `D5/S3/Arith/ModularForms/CubicThetaOddParity.coreOddEquiv`
- Dependency: [D5/S3/Arith/ModularForms/CubicThetaCoreProduct](CubicThetaCoreProduct.md)
