# Two Squares Cover Every Prime Residue Field

## Abstract

Every residue modulo a prime is the sum of two residue squares.

**Theorem 1.1 (Every prime residue is a sum of two squares).**

$$\forall p\in\mathbb{N}, p\ \text{prime}, \forall x\in\mathbb{Z}/p\mathbb{Z}, \exists a,b\in\mathbb{Z}/p\mathbb{Z}, a^{2}+b^{2}=x$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/FiniteFieldTwoSquares.every_element_eq_sq_add_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and every residue x modulo p, there are residues a and b whose squared sum is x. This includes p = 2 and adds no uniqueness or canonical-choice claim for the witnesses.

Pinned Mathlib already contains the exact theorem as ZMod.sq_add_sq in Mathlib.FieldTheory.Finite.Basic. The Lean declaration directly applies that result and does not reproduce its finite-field proof.

## References

- Truth anchor: `D5/S3/ArithUnits/FiniteFieldTwoSquares.every_element_eq_sq_add_sq`
