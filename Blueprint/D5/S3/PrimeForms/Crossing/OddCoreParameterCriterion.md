# Odd-Core Parameter Criterion

## Abstract

A positive square root has a unique exchange parameter exactly when twice it divides the gcd.

**Theorem 1.1 (Square and gcd data determine the exchange parameter).**

$$\forall m, b, c\in \mathbb{N},\ \left(\exists x\in \mathbb{N},\ x^{2}=m \land 0<x \land \exists! y\in \mathbb{N},\ 2\times x\times y=\gcd(b, c)\right) \iff \left(\exists x\in \mathbb{N},\ x^{2}=m \land 0<x \land 2\times x \mid \gcd(b, c)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Crossing/OddCoreParameterCriterion.odd_core_parameter_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a positive natural square root x of m. A witness for divisibility of gcd(b,c) by 2x is exactly a parameter y satisfying 2xy = gcd(b,c). Positivity makes 2x nonzero, so cancellation shows that two such parameters must agree.

Repository and pinned-Mathlib searches found no equivalent combined criterion. Loogle found no matching divisibility equivalence or gcd equation; its only unique-multiplier result concerned field inverses. The proof reuses Mathlib's divisibility witness and positive natural multiplication cancellation.

This closes the square/gcd exchange-parameter criterion in appendix E.44. It does not assert the geodesic interpretation, the remaining determinant equation, or the finite census.

## References

- Truth anchor: `D5/S3/PrimeForms/Crossing/OddCoreParameterCriterion.odd_core_parameter_criterion`
