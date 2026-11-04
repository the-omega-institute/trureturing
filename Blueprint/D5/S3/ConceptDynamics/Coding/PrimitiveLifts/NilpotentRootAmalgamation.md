# Unique coprime root amalgamation in nilpotent groups

## Abstract

Nilpotency makes equal coprime powers arise from exactly one common root, without excluding torsion or infinite groups.

**Theorem 1.1 (Exact unique common root).**

$$\forall G \in Type,\; [\operatorname{Group}\left(G\right)][\operatorname{IsNilpotent}\left(G\right)]\forall x \in G, y \in G, m \in Nat, n \in Nat,\; (\operatorname{Coprime}\left(m, n\right) \implies (x^{m} = y^{n} \iff \exists z \in G,\; ((x = z^{n} \land y = z^{m}) \land \forall w \in G,\; ((x = w^{n} \land y = w^{m}) \implies w = z))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/NilpotentRootAmalgamation.pow_eq_pow_iff_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group G with Group.IsNilpotent G, every x,y:G and every coprime m,n:Nat, x^m=y^n holds if and only if there exists exactly one z:G satisfying x=z^n and y=z^m. The group may be infinite, noncommutative and have torsion. If either exponent is zero, coprimality forces (m,n)=(0,1) or (1,0), and the equations respectively give y=1 with z=x, or x=1 with z=y.

First, central-quotient induction proves that Commute(x^m,y) and Commute(x,y^n) force Commute(x,y). The quotient induction makes the commutator central. Its mth and nth powers then equal the two trivial power commutators, and coprimality kills it. Equal powers supply precisely these commuting hypotheses. This adapts the established central-quotient argument in Mathlib's Group.IsNilpotent.commute_of_orderOf_coprime; equality of coprime powers does not imply that the element orders are coprime.

Choose integers A=Nat.gcdA m n and B=Nat.gcdB m n, so m*A+n*B=1. Since x and y commute, z=x^B*y^A has the required powers. For every candidate w the same identity reconstructs w=(w^n)^B*(w^m)^A=x^B*y^A, proving uniqueness. This is uniqueness from the two specified powers together; it makes no assertion that an individual power map is injective. For example the quaternion group has distinct elements with equal squares. The converse only uses the commutation of powers of one element and holds in every group.

The reused inputs are the pinned Mathlib nilpotent_center_quotient_ind, commutatorElement_pow_left/right, pow_eq_one_iff_of_coprime and the integer Bezout identity Nat.gcd_eq_gcd_ab. Mathlib's similarly named Commute.pow_eq_pow_iff_of_coprime is stated for GroupWithZero and is not applied to an ordinary group. These are mature commutator and Bezout methods; their combination here is a repository derivation, with no claim of literature priority.

For root compatibility in signed return charts, this identifies a structural setting in which prescribed coprime roots amalgamate. In particular, a homomorphism from the coprime torus-knot presentation with generators x,y and relation x^m=y^n into a nilpotent group has cyclic two-generator image, because both images are powers of z and z is their integer word. Separate roots in an arbitrary nonnilpotent group need not have this compatibility. This is an interpretation of the theorem, not an additional formal declaration.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PrimitiveLifts/NilpotentRootAmalgamation.pow_eq_pow_iff_exists_unique`
