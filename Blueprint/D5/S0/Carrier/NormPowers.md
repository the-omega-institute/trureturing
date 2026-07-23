# Golden Norm Powers

## Abstract

The golden norm carries natural powers to integer powers.

**Theorem 1.1 (Norm of a natural power).**

$$\forall x\in\mathbb{Z}[\varphi],\ \forall n\in\mathbb{N},\ N(x^n)=N(x)^n$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/NormPowers.norm_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing norm is packaged as a monoid homomorphism from `GoldenInt` to `Int`. Applying its standard power law gives the exact identity for every golden integer and every natural exponent, with no extra algebraic assumptions.
