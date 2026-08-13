# Discrepancy and Density of Lower Mechanical Words

## Abstract

General discrepancy and density for lower mechanical words.

For every real slope alpha in the half-open interval from zero to one, every real intercept rho, and every window start, the lower mechanical true count differs from its expected count by strictly less than one. Dividing by the window length then gives the density alpha at every fixed start; no irrationality assumption is used.

**Theorem 1.1 (Every lower mechanical window has discrepancy below one).**

$$\left|\operatorname{windowTrueCount}\left(alpha, rho, i, n\right) - n \cdot alpha\right| < 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing endpoint-floor telescope rewrites the count difference as the difference of two fractional parts. Nonnegativity and strict upper bounds for those fractional parts give both sides of the absolute-value inequality.

**Theorem 1.2 (Every fixed-start lower mechanical density tends to the slope).**

$$\lim_{n\to\infty}\frac{\operatorname{windowTrueCount}\left(alpha, rho, i, n\right)}n=alpha.$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive window lengths, the discrepancy inequality places the quotient between alpha minus 1 over n and alpha plus 1 over n. Both bounds converge to alpha, so the squeeze theorem proves the fixed-start density limit.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_density`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_discrepancy`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
