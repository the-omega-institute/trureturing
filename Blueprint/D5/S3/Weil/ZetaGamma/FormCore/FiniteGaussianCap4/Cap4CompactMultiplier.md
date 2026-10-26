# Signed compact multiplier bounds

## Abstract

Signed compact multiplier bounds

**Theorem 1.1 (Uniform control of the signed correction).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.compactDebit_abs_le_four`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.compactDebit_abs_le_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define C(x)=(x/pi)^(5/2)-4*(x/pi)^(-7/2) for x>pi, and zero otherwise. Define B(x)=x^2/10-C(x) for 0<x<6, and zero otherwise. For every real x, |B(x)|<=4, including both endpoints and negative x.

The proof bounds sqrt(x/pi) and its reciprocal power on the annulus 1<=x/pi<=2, together with 9<=pi^2<=10. It controls both signs of B; no sampled or unsigned substitute is used.

**Theorem 1.2 (Domination on the whole nonnegative half-line).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.capWeight_ge_quadratic_minus_compact`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.capWeight_ge_quadratic_minus_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real x>=0, x^2/10-B(x)<=C(x). Inside the correction interval this is exact. At x=0 the definitions give equality; for x>=6 a separate power comparison proves the inequality without compact truncation of the domain.

These are repository-derived pointwise analytic estimates using existing real-power and pi bounds. They supply multiplier control only; the physical source graph, matrix enclosures, and final quotient require separate proofs.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.capWeight_ge_quadratic_minus_compact`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4CompactMultiplier.compactDebit_abs_le_four`
