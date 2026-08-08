# Units Modulo a Prime

## Abstract

An element modulo a prime is a unit exactly when it is nonzero.

**Theorem 1.1 (An element modulo a prime is a unit exactly when it is nonzero).**

$$\forall p \text{prime},\quad\forall a \in \mathbb{Z}/p\mathbb{Z},\quad\operatorname{IsUnit}(a) \Leftrightarrow a \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/PrimeModUnit.prime_modulus_is_unit_iff_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and every residue a modulo p, this theorem identifies the multiplicatively invertible residues exactly with the nonzero residues. Both directions are substantive: zero has no multiplicative inverse, while primality ensures that every nonzero residue has one.

Mathlib already supplies the general equivalence isUnit_iff_ne_zero for groups with zero and the field instance for ZMod p under a primality Fact. The Lean proof only installs that Fact from the explicit Nat.Prime hypothesis and applies the existing equivalence, so this is a thin repository-addressed wrapper rather than a second proof.

## References

- Truth anchor: `D5/S3/ArithUnits/PrimeModUnit.prime_modulus_is_unit_iff_ne_zero`
