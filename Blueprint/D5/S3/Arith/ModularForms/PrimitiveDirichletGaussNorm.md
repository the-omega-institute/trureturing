# Primitive Dirichlet Gauss norm

## Abstract

The Gauss sum of a primitive Dirichlet character modulo a prime has squared complex modulus equal to that prime.

**Theorem 1.1 (Prime-modulus primitive Dirichlet Gauss norm).**

Lean statement: `D5/S3/Arith/ModularForms/PrimitiveDirichletGaussNorm.primitive_dirichlet_gauss_normSq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/PrimitiveDirichletGaussNorm.primitive_dirichlet_gauss_normSq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural prime p, a nonzero modulus instance, and a primitive character χ : DirichletCharacter ℂ p, the squared complex modulus of the standard additive-character Gauss sum is p. The proof combines Mathlib's primitive Gauss product with conjugation of both characters and the identity Fintype.card (ZMod p) = p. This is the normalization bridge for primitive Dirichlet modular-form twists; the q-expansion coefficient law remains open.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/PrimitiveDirichletGaussNorm.primitive_dirichlet_gauss_normSq`
