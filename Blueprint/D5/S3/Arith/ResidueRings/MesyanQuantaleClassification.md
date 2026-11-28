# Classification of additive-submonoid quantale units in rings

## Abstract

A ring has a quantale unit on its additive submonoids exactly when it has a ring unit or is a torsion ring with unital primary components.

**Theorem 1.1 (The ring classification in Mesyan's Question 36).**

$$\forall (R: Type), [NonUnitalRing R], (\exists (E: AddSubmonoid R), \forall (M: AddSubmonoid R), E \cdot M = M \land M \cdot E = M) \Leftrightarrow (\exists (u: R), \forall (x: R), u \cdot x = x \land x \cdot u = x) \lor ((\forall (a: R), 0 < addOrderOf(a)) \land (\forall (p: Primes), \exists (u: R), (\exists (j: \mathbb{N}), p^{j} \cdot u = 0) \land (\forall (x: R), (\exists (j: \mathbb{N}), p^{j} \cdot x = 0) \Rightarrow (u \cdot x = x \land x \cdot u = x))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff` (`✓ std3`). ∎

*Resolves.* `Problems/mesyan-2026-question-36-ring-classification` (proved) by `D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mesyan-2026-question-36-ring-classification","declaration_gid":"D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Let R be an associative ring with no assumed identity or commutativity. In Definition 4, the product of two additive submonoids consists of sums of a positive finite number of ordered pairwise products. This is Mathlib's additive-submonoid multiplication. It contains zero through the one-term sum of the product of two zeros. The shared reference for Definition 4 and Question 36 is `D5/L/ArithUnits/mesyan2026quantales`.

The quantale has a two-sided identity precisely if R has a two-sided multiplicative identity or its additive group is torsion and each prime-primary component has a two-sided identity belonging to that component. The component for p consists of elements killed by some natural power of p, with inherited ring operations. The dot after a prime power denotes repeated addition. Zero serves as the identity in a zero component and in the zero ring. The formula uses positive additive order for torsion since infinite additive order is represented by zero. The classification concerns the ring case of Question 36.

Testing a quantale unit on cyclic additive submonoids shows that each multiplier acts by natural multiples and that each element has a fixing multiplier. An infinite-order fixed point forces the left action to be injective and idempotent, giving a left identity. An order-p fixed point forces injectivity on the p-primary component. There the action is a scalar coprime to p, which can be inverted using a power of p that kills the projected multiplier. Passing to the opposite ring gives the corresponding right identities, and the left and right identities coincide.

A ring identity gives a quantale unit by taking its natural multiples. For a torsion ring, the primary identities can be added over the finite primary support of each element to fix it on both sides. Products between distinct primary components vanish, and the Chinese remainder theorem expresses each such action as a natural multiple on every argument. The additive submonoid of multipliers whose left and right actions agree with a natural multiple on each argument is then a two-sided quantale unit.

## References

- Truth anchor: `D5/S3/Arith/ResidueRings/MesyanQuantaleClassification.product_unit_iff`
