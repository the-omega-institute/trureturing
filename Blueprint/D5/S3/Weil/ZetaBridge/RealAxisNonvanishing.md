# Real-Axis Zeta Zeros Outside the Unit Interval

## Abstract

Real zeta zeros outside the open unit interval are negative even integers.

**Theorem 1.1 (Real zeros outside the open unit interval are trivial).**

$$\forall x: \mathbb{R},\\{}(\neg ((0 < x) \land (x < 1))) \Rightarrow ((\operatorname{riemannZeta}\left(x\right) = 0) \Rightarrow (\exists n: \mathbb{N}, x = -2 * (n + 1))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/RealAxisNonvanishing.riemannZeta_real_zero_outside_Ioo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive real input outside the open unit interval, Mathlib's nonvanishing theorem for real part at least one excludes a zero.

For a nonpositive input, the completed-zeta quotient and its frozen nonvanishing on the closed left half-plane force the real gamma factor to vanish. Mathlib's gamma-zero classification then gives a negative even integer, with zero excluded by the value of zeta at zero.

This is pure Mathlib content. It neither constructs zeta zeros nor makes a claim about the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/RealAxisNonvanishing.riemannZeta_real_zero_outside_Ioo`
