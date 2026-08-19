# Reciprocal Balance

## Abstract

Reciprocal antisymmetry forces balance at every negative-norm metallic root.

**Theorem 1.1 (Reciprocal symmetry forces metallic balance).**

$$\forall n\in \mathbb{N}, s: \mathbb{R} \to \mathbb{R}, (\forall x\in \mathbb{R}, s(x+1)=s(x)) \land s(\frac{1}{m_{n}})=-s(m_{n}) \Rightarrow s(m_{n})=0.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/ReciprocalBalance.metallic_reciprocal_symmetry_forces_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here m_n is the positive metallic root (n + sqrt(n^2 + 4))/2. Its frozen reciprocal identity is 1/m_n = m_n - n. Unit periodicity identifies the slope at those two arguments, while reciprocal antisymmetry identifies the same value with its negative; characteristic zero then forces zero.

The proof directly reuses the repository theorem metallic_family_value and Mathlib's Periodic.sub_nat_mul_eq and CharZero.eq_neg_self_iff. No reciprocal identity, periodic transport law, or characteristic-zero cancellation is reproved here.

This is an honest partial closure of only the norm-minus-one balance sentence in source remark 27.135. Existence of the Cesaro-log slope, the reciprocal sign law, the excess formula, the norm-plus-one slope formula, and every numerical certificate remain outside this theorem.

## References

- Truth anchor: `D5/S1/Eigenstructure/ReciprocalBalance.metallic_reciprocal_symmetry_forces_balance`
