# Discrepancy and Density of Lower Mechanical Words

## Abstract

For every real slope alpha with `0 <= alpha < 1`, every real intercept rho, and every
window start, lower mechanical true counts have a uniform strict discrepancy bound. The
corresponding quotient converges to alpha at each fixed start. No irrationality assumption
is used.

**Theorem 1.1 (Every lower mechanical window has discrepancy below one).**

$$
\left|\operatorname{lowerMechanicalWindowTrueCount}(\alpha,\rho,i,n)-n\alpha\right|<1
$$

*Proof.* Machine-checked in Lean as
`D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_discrepancy`
(`✓ std3`). ∎

The existing endpoint-floor telescope rewrites the count as a difference of endpoint
floors. Writing each endpoint as its floor plus fractional part leaves the error as the
difference of two fractional parts. `Int.fract_nonneg` and `Int.fract_lt_one` at both
endpoints give the two strict inequalities.

**Theorem 1.2 (Every fixed-start lower mechanical density tends to the slope).**

$$
\lim_{n\to\infty}
\frac{\operatorname{lowerMechanicalWindowTrueCount}(\alpha,\rho,i,n)}{n}=\alpha
$$

*Proof.* Machine-checked in Lean as
`D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_density`
(`✓ std3`). ∎

For `n >= 1`, divide the discrepancy bound by the positive real cast of `n`. The quotient
is squeezed between `alpha - 1/n` and `alpha + 1/n`; both bounds tend to alpha.

The private rational check in the Lean module evaluates the boundary-free case
`alpha = 1/3`, `rho = 0`, `i = 0`, `n = 3`, confirming the strict bound by kernel reduction.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_discrepancy`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalDensity.lower_mechanical_window_true_density`
- Dependency: [D5/S1/Words/Mechanical/MechanicalBalance](MechanicalBalance.md)
