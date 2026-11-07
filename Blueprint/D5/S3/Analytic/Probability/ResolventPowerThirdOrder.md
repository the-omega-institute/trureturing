# Third order probability Stieltjes bounds

## Abstract

Actual third derivatives of real powers of normalized probability Stieltjes transforms, including arbitrary laws and endpoint atoms.

**Definition 1.1 (The normalized integral transform).**

Lean statement: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.stieltjes`

*Formalization.* `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.stieltjes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a measure mu on an arbitrary measurable space Omega and a real function R, K(s) is the Bochner integral of (1+R(omega)s)^(-1) against mu. For the theorems mu is a probability measure, R is measurable, and 0<=R<=1 almost everywhere. In particular K(0)=1. Discrete, singular, continuous and mixed laws are included; atoms at zero and one are allowed.

**Definition 1.2 (The real power curve).**

Lean statement: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve`

*Formalization.* `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a, q and s, G(s)=(1+as)^(q+1) K(s)^q, with both powers interpreted as Real.rpow. This is the actual function defined from the integral. Near zero both bases are positive. The derivative formulas allow arbitrary real a and q; the inequalities assume 0<=a<=1 and q>0.

**Theorem 1.3 (Actual second and third derivatives).**

Lean statement: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability measure mu on every measurable space Omega, and every measurable R with values in [0,1] almost everywhere, let m=E[R], M2=E[R^2], M3=E[R^3], v=M2-m^2, tau=M3-3mM2+2m^3 and delta=a-m. For all real a and q, iteratedDeriv 2 G 0=q(q+1)delta^2+2qv and iteratedDeriv 3 G 0=q((q+1)delta^2((q-1)delta-3m) +6((q+1)delta-m)v-6tau). No smoothness or moment premise is required. On |s|<1/2 the n-th inverse kernel has absolute value at most n! 2^(n+1); dominated differentiation gives a genuine derivative chain. The real power and product rules identify the displayed expressions with the iterated derivatives.

**Theorem 1.4 (The probability-law third order bounds).**

Lean statement: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve_third_order`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve_third_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability measure mu on every measurable space Omega, every measurable R with 0<=R<=1 almost everywhere, every a in [0,1] and every real q>0, one has G''(0)>=0. If q>=1, then G'''(0)<=(q-1)G''(0). If q<=1, then G'''(0)<=0. All derivatives in this statement are actual iteratedDeriv values. The variance satisfies 0<=v<=m(1-m). Integrating the nonnegative weighted square R(xR-y)^2 gives the raw moment minor M2^2<=mM3 when m>0, as well as E[R(R-a)^2]>=0. For 0<q<=1, square completion bounds G'''(0)/q by (q^2-1)delta^2(a+m/2) -(6/m)(v-(q+1)m delta/2)^2. The m=0 case is handled separately, without dividing by a vanishing mean. For q>=1, the deficit is a sum of E[R(R-a)^2] and nonnegative terms; the variance bound is used when delta>1/3. Degenerate laws and zero curvature are retained.

These are reusable scalar probability and analysis results for Stieltjes transforms and real power curves, motivated by entropy and divergence estimates. The derivation is repository mathematics using Mathlib calculus, integrals and variance inequalities. No literature novelty claim, matrix representation supplier, rank-one matrix bridge, or resolution of the full He-Saunderson-Fawzi matrix conjecture is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve`
- Truth anchor: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve_derivatives`
- Truth anchor: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.powerCurve_third_order`
- Truth anchor: `D5/S3/Analytic/Probability/ResolventPowerThirdOrder.stieltjes`
