# Finite Character Orthogonality

## Abstract

A nontrivial multiplicative character on a finite group has zero total sum, and a unitary character has one unit of norm-square mass per group element.

**Theorem 1.1 (A nontrivial finite-group character sums to zero).**

$$\forall G: \operatorname{Type},\ \operatorname{Group}(G) \land \operatorname{Fintype}(G),\ chi: \operatorname{MonoidHom}(G, Complex), chi \neq 1 \Rightarrow \sum g\in G chi(g) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality.nontrivial_character_sum_eq_zero` (`✓ std3`). ∎

*Citation.* Rudolf Lidl; Harald Niederreiter (1997). *Finite Fields*. URL: <https://doi.org/10.1017/CBO9780511525790>.

*Commentary.*

For a finite group G and a multiplicative character χ that is not the trivial character, the sum of χ over G vanishes.

Choose a with χ(a) ≠ 1. Left translation by a permutes G, so multiplying the sum by χ(a) leaves it unchanged. Cancellation in ℂ then forces the sum to be zero.

This is the finite algebraic orthogonality input used in Gauss-sum and Hasse--Davenport arguments. It does not supply the analytic Hecke action or the Hasse--Davenport product formula.

**Proposition 1.2 (A unitary character has exact norm-square mass).**

$$\forall G: \operatorname{Type},\ \operatorname{Group}(G) \land \operatorname{Fintype}(G),\ chi: \operatorname{MonoidHom}(G, Complex),\ \forall g: G, \left\lVert chi(g) \right\rVert=1 \Rightarrow \sum g\in G \left\lVert chi(g) \right\rVert^2 = \operatorname{card}(G).$$

*Proof.* Machine-checked in Lean as `D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality.unitary_character_norm_sq_sum_eq_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the character takes values on the unit circle, every summand has squared norm one, so the total norm-square mass is exactly the finite group cardinality.

The unit-modulus hypothesis is explicit: an arbitrary monoid hom into ℂ need not be unitary. This normalization is the one consumed by the standard Gauss-sum norm calculation.

## References

- Truth anchor: `D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality.nontrivial_character_sum_eq_zero`
- Truth anchor: `D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality.unitary_character_norm_sq_sum_eq_card`
- Dependency: [D5/S3/Arith/FiniteFieldQuadraticCharacterSum](../../../S3/Arith/FiniteFieldQuadraticCharacterSum.md)
