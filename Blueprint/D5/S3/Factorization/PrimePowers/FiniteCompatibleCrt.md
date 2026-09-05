# Finite Compatible CRT

## Abstract

Finite congruences glue exactly under pairwise gcd compatibility, uniquely modulo lcm.

**Theorem 1.1 (Finite CRT gluing and integer representatives).**

$$\forall I: Type, [\operatorname{Fintype}(I)], m: I \to \mathbb{N}, a: I \to \mathbb{Z}, ((\forall i: I, \forall j: I, i \neq j \Rightarrow \operatorname{Coprime}(m(i), m(j))) \Rightarrow \exists! z: \operatorname{ZMod}(\prod_{i \in I} m(i)), \forall i: I, \operatorname{pi}(i, z) = a(i)) \land ((\forall i: I, \forall j: I, \operatorname{ModEq}(\operatorname{gcd}(m(i), m(j)), a(i), a(j))) \iff (\exists x: \mathbb{Z}, \forall y: \mathbb{Z}, ((\forall i: I, \operatorname{ModEq}(m(i), y, a(i))) \iff \operatorname{ModEq}(\operatorname{lcm}_{i \in I} m(i), y, x)))) \land ((\forall i: I, m(i) \neq 0) \Rightarrow \forall x: \mathbb{Z}, \exists y: \mathbb{Z}, y \neq x \land (\forall i: I, \operatorname{ModEq}(m(i), y, x))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt.finite_crt_gluing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The index type I is finite, m assigns natural moduli, and a assigns integer representatives of the local data. P is the product of all m(i), L is their finite least common multiple, and pi(i,z) is the canonical ZMod castHom from modulus P to modulus m(i). The right side a(i) of the first equality is cast into ZMod(m(i)).

ModEq(n,x,y) means integer congruence modulo n. The middle clause identifies the entire solution set with one congruence class modulo L; setting y=x also supplies a simultaneous solution. Empty index types are included, with P=L=1. Zero moduli are allowed in the first two clauses; ZMod(0) records the whole integer.

The last clause assumes nonzero natural moduli, hence positive moduli. Adding P gives a distinct integer with the same finite residue data. Selecting an ordinary integer therefore requires additional restrictions such as a suitable bounded interval; sign alone is not asserted to suffice.

The proof imports the frozen binary compatible-residue image theorem. Finite induction derives compatibility between a merged solution and the next residue across gcd(L,m(j)), using gcd distribution over finite lcm, and then applies binary gluing. The coprime clause uses pinned Mathlib's ZMod.prodEquivPi.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt.finite_crt_gluing`
- Dependency: [D5/S3/Factorization/PrimePowers/CompatibleResidueJointImage](CompatibleResidueJointImage.md)
