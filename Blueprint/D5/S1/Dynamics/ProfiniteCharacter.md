# Continuous Characters of the Profinite Integers

## Abstract

Continuous profinite-integer characters factor through a finite residue coordinate.

**Theorem 1.1 (Every continuous character has finite level).**

$$\operatorname{FactorsThroughFiniteResidue}\left(chi\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/ProfiniteCharacter.continuous_character_factors_through_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A basic neighborhood of zero constrains finitely many residue coordinates, whose product supplies one common modulus. Continuity sends the resulting coordinate kernel into a small arc of the circle. Since a subgroup contained in that arc is trivial, the character vanishes on the coordinate kernel and therefore descends to the finite cyclic quotient.

The finite quotient character is then determined by its value at one. The pinned library supplies the no-small-subgroup lemma for the circle, the classification of finite-order circle points, and standard finite cyclic characters. It does not supply the profinite finite-level factorization proved here.

## References

- Truth anchor: `D5/S1/Dynamics/ProfiniteCharacter.continuous_character_factors_through_residue`
