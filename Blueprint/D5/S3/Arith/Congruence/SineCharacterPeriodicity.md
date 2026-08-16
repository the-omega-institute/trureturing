# Sine and the Character Modulo Four

## Abstract

Sine at integer half-turns is the quadratic character modulo four.

**Theorem 1.1 (Integer half-turn sine equals the character modulo four).**

$$\forall n \in \mathbb{N}, \sin(\frac{\pi n}{2}) = \operatorname{chi}_{4}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/SineCharacterPeriodicity.sin_pi_mul_nat_div_two_eq_chi_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number n, sine at pi n divided by two equals the real cast of the quadratic character modulo four. Thus the values on residue classes 0, 1, 2, and 3 are respectively 0, 1, 0, and -1.

Pinned Mathlib was searched before proving. It has no exact theorem assembling this sine-character equality, but Real.sin_add_nat_mul_two_pi supplies the period reduction, Real.sin_pi_div_two and Real.sin_add_pi evaluate the odd residues, and ZMod.chi-four-nat-mod-four supplies character periodicity. The Lean proof composes those declarations after quotient-remainder reduction.

This closes only the explicit sine-pattern bridge in residual remark 27.9. It does not formalize the Gauss-Jacobi two-squares formula, the associated Dirichlet-series factorization, or the evaluation of the L-series at one.

## References

- Truth anchor: `D5/S3/Arith/Congruence/SineCharacterPeriodicity.sin_pi_mul_nat_div_two_eq_chi_four`
