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

Application to complementary-width circular windows. Take an arbitrary real slope alpha strictly between zero and one, initial phase u and window centre c. Set the width w to one minus alpha, the left endpoint a to c minus w over two, and the mechanical intercept rho to u minus a. A positive integer time k is a hit exactly when the fractional part of u plus k times alpha minus a is less than w. This defines a left-closed, right-open circular window. Let H(N) count hits at precisely times one through N, with an empty count when N is zero.

The lower mechanical letter at time k is the floor increment from rho plus k times alpha to rho plus (k plus one) times alpha. It is either zero or one, and equals one exactly when the starting fractional part is at least one minus alpha. Thus a hit is the complement of a true letter. Equality at the carry threshold is excluded from the window. The exact count correspondence is $\operatorname{H}\left(N\right) = N - \operatorname{windowTrueCount}\left(alpha, rho, 1, N\right)$. The start index is one, rather than zero.

Apply the discrepancy result with this intercept, start index one and length N. The hit discrepancy is the negative of the true-letter discrepancy, so $\left|\operatorname{H}\left(N\right) - N \cdot w\right| < 1$ for every natural N, including zero. The endpoint-floor identity in `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWindowTrueCount_eq_floor` expresses that discrepancy exactly as $\operatorname{H}\left(N\right) - N \cdot w = \operatorname{fract}\left(rho + \left(N + 1\right) \cdot alpha\right) - \operatorname{fract}\left(rho + alpha\right)$. Both fractional parts lie in the half-open unit interval.

For positive N, division gives frequency error strictly below one over N, uniformly in the initial phase, window centre and slope subject to this width relation. In particular the frequency tends to w. Taking alpha to be the golden ratio minus one gives width two minus the golden ratio. Taking a fractional part before the window test gives the identical predicate because $\operatorname{fract}\left(\operatorname{fract}\left(x\right) - a\right) = \operatorname{fract}\left(x - a\right)$. No irrationality premise is needed. The conclusion uses width one minus alpha and does not classify arbitrary independent window widths, certify floating-point evaluation or supply a physical interpretation.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalBalance.lowerMechanicalWindowTrueCount_eq_floor`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_density`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_discrepancy`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
