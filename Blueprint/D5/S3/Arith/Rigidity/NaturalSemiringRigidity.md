# Natural Semiring Automorphism Rigidity

## Abstract

Every semiring automorphism of the natural numbers is the identity.

**Theorem 1.1 (Every natural semiring automorphism is the identity).**

$$\forall e \in \operatorname{Aut}_{sr}(\mathbb{N}), e = \mathrm{id}_{\mathbb{N}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Rigidity/NaturalSemiringRigidity.natural_semiring_automorphism_is_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A semiring automorphism of the natural numbers preserves every natural number because each natural is generated from zero and one by addition. Mathlib's map_natCast supplies this pointwise equality, and RingEquiv.ext promotes it to equality with the identity automorphism.

This node formalizes only the claim in remark 27.15 that the additive structure collapses natural-number automorphisms to the identity. It does not formalize the atom's claims about Spec Z, program complexity, zeta, the Riemann hypothesis, or permutations in the multiplication-only structure.

## References

- Truth anchor: `D5/S3/Arith/Rigidity/NaturalSemiringRigidity.natural_semiring_automorphism_is_identity`
