# Cancellation Under Group Inversion

## Abstract

An inversion-antisymmetric integer-valued function sums to zero on a finite group.

**Theorem 1.1 (Inversion antisymmetry forces total cancellation).**

$$\forall G \operatorname{finite group},\ \forall f: G \to \mathbb{Z},\ (\forall g: G,\ f(g^{-1}) = -f(g)) \Rightarrow \sum_{g\in G} f(g) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Symmetry/InversionAntisymmetricSum.inversion_antisymmetric_sum_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a finite group and let f be integer-valued. If f sends the inverse of every group element to the negative of its value, then the sum of f over G is zero. Distinct inverse pairs cancel, while any self-inverse element has value equal to its own negative and hence has value zero in the integers.

The Lean proof is a thin specialization of Mathlib's Finset.sum_ninvolution to inversion on the universal finite set. It also reuses Equiv.inv for the pairing and CharZero.eq_neg_self_iff for fixed points. Repository and pinned-Mathlib searches found no end-to-end theorem for this exact finite-group sum.

This closes only the sentence in appendix E.110 stating that inversion changes sign and therefore the total finite-circle sum is zero. It does not assert the negative-continued-fraction bijection, the class-number law, or any other clause of that residual atom.

## References

- Truth anchor: `D5/S3/PrimeForms/Symmetry/InversionAntisymmetricSum.inversion_antisymmetric_sum_eq_zero`
