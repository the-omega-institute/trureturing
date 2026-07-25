# Norm Powers

## Abstract

The golden norm preserves natural powers through its monoid homomorphism.

**Theorem 1.1 (Golden norm power law).**

$$\forall x\in\mathbb{Z}[\varphi],\ \forall n\in\mathbb{N},\ N(x^n)=N(x)^n.$$

*Proof.* Machine-checked in Lean as `D5/S0/Carrier/NormPowers.norm_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplicative norm has already been packaged as `normMonoidHom`, so the natural-power law follows from the generic power preservation law for monoid homomorphisms. This generalizes the existing `phi` power computation without introducing new coordinate algebra.
