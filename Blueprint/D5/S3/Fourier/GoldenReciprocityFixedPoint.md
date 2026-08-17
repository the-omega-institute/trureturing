# Golden Reciprocity at Its Fixed Point

## Abstract

Golden reciprocity and unit periodicity determine the value at the golden fixed point.

**Theorem 1.1 (The reciprocal golden argument closes the functional equation).**

$$x = \frac{1}{\varphi},\quad Periodic(c, 1),\\\forall y, Irrational(y) \Rightarrow g(y) = y \cdot c(y) + c(\frac{1}{y}),\\\Rightarrow c(x) \cdot (x + 1) = g(x) \land c(x) = \frac{g(x)}{\varphi}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/GoldenReciprocityFixedPoint.golden_reciprocity_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be periodic with period one and suppose that at every irrational argument y the reciprocal relation is g(y) = y c(y) + c(1/y). Set x = 1/phi. Since 1/x = phi = x + 1, periodicity identifies c(1/x) with c(x).

Substitution gives g(x) = (x + 1)c(x). The pinned Mathlib golden-ratio identities identify x + 1 with phi, and division by the nonzero golden ratio yields c(x) = g(x)/phi.

This closes only the leading exact fixed-point equation and its value consequence in theorem-form 6.190, clause 2. It does not claim the later numerical extrapolation, decimal values, method assessment, or the registration statements in that atom.

## References

- Truth anchor: `D5/S3/Fourier/GoldenReciprocityFixedPoint.golden_reciprocity_fixed_point`
