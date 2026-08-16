# Finite Cyclic Homomorphism Rigidity

## Abstract

A finite cyclic group has no nonzero additive homomorphism to a torsion-free group.

**Theorem 1.1 (Every map from a finite cyclic group to a torsion-free group is zero).**

$$\forall n : \mathbb{N}, n \neq 0, \forall A, \mathrm{IsAddTorsionFree}{A}, \forall f \in \mathrm{Hom}{\mathrm{ZMod}{n}, A}, f = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/CyclicTorsionFreeHomRigidity.zmod_hom_to_torsion_free_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let n be nonzero and let A be a torsion-free additive commutative monoid. Every additive homomorphism f from ZMod n to A is the zero homomorphism. The source has characteristic n, so n times every source element is zero. Mapping this equality through f and using injectivity of multiplication by the nonzero integer n in A forces every value f(x) to be zero.

The proof directly reuses mathlib's ZModModule.char_nsmul_eq_zero and nsmul_right_injective. Specializing n to 12 and A to the additive real numbers establishes Hom(Z/12Z, R) = 0, the torsion consequence used in appendix E.20. This node does not formalize the abelianization computation for PSL(2,Z), the bounded Euler-class defect formula, or the later quasimorphism classification.

## References

- Truth anchor: `D5/S3/Arith/Congruence/CyclicTorsionFreeHomRigidity.zmod_hom_to_torsion_free_eq_zero`
