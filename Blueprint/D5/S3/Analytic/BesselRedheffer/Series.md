# The normalized Bessel series

## Abstract

Convergence and differential identities of the normalized Bessel series.

**Definition 1.1 (The normalized coefficients).**

$$\forall b \in \mathbb {R},\; \forall n \in \mathbb {N},\; \operatorname {coeff}\left(b, n\right) = \frac{1}{\operatorname {Nat.factorial}\left(n\right) \cdot \operatorname {Polynomial.eval}\left(b, \operatorname {ascPochhammer}\left(\mathbb {R}, n\right)\right)}$$

*Formalization.* `D5/S3/Analytic/BesselRedheffer/Series.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is the reciprocal of the factorial times the rising factorial.

**Theorem 1.2 (The coefficient recurrence).**

$$\forall b \in \mathbb {R},\; 0 < b \Rightarrow \left(\forall n \in \mathbb {N},\; \operatorname {coeff}\left(b, n + 1\right) = \frac{\frac{1}{b + n}}{n + 1} \cdot \operatorname {coeff}\left(b, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.coeff_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive lower parameter, the rising-factorial and factorial recurrences determine the next coefficient.

**Theorem 1.3 (Absolute convergence at every argument).**

$$\forall b \in \mathbb {R},\; 0 < b \Rightarrow \left(\forall t \in \mathbb {R},\; \operatorname {Summable}\left(n: \mathbb {N}\mapsto \left\lVert \operatorname {coeff}\left(b, n\right) \cdot t^{n} \right\rVert\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.summable_norm_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive lower parameter and every real t, the weighted coefficient series is absolutely summable.

**Theorem 1.4 (Absolute convergence).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.summable_nbessel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.summable_nbessel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For order nu greater than -1 and every real argument x, the defining series converges absolutely. The ratio of successive coefficient magnitudes is 1/((nu+1+n)(n+1)); multiplying by any fixed argument still gives a sequence tending to zero.

**Theorem 1.5 (The value at the origin).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.nbessel_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real order nu the value at zero is one, since only the constant term contributes.

**Theorem 1.6 (Differentiation raises the order).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu greater than -1, the derivative at every real x is -x/(2(nu+1)) times the normalized Bessel function of order nu+1. The auxiliary series in t=-x squared/4 has derivative equal to the series with its lower parameter raised by one, divided by the original lower parameter. On a bounded interval the differentiated series has an absolutely summable uniform majorant.

**Theorem 1.7 (Continuity).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.continuous_nbessel`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.continuous_nbessel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu greater than -1, the normalized Bessel function is continuous on the real line.

**Theorem 1.8 (Positivity near zero).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_pos_near_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.nbessel_pos_near_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu greater than -1 the normalized series is positive in a neighbourhood of zero, since it is continuous and its value at zero is one.

**Theorem 1.9 (Three consecutive orders).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_contiguous`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.nbessel_contiguous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu greater than -1, the series of order nu equals the series of order nu+1 minus x squared divided by 4(nu+1)(nu+2) times the series of order nu+2. The rising factorial recurrence gives the coefficient identity and absolute convergence permits summation.

**Theorem 1.10 (A second derivative).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nu greater than -1, the derivative of -x/(2(nu+1)) times the series of order nu+1 is -1/(2(nu+1)) times that series plus x squared divided by 4(nu+1)(nu+2) times the series of order nu+2.

**Theorem 1.11 (The normalized Bessel equation).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_ode`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Series.nbessel_ode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second derivative multiplied by x, plus the first derivative multiplied by 2nu+1, plus x times the normalized series, vanishes for every real x and every nu greater than -1. Substituting the shifted-series derivative formulas reduces the identity to the relation between three consecutive orders.

## References

- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.coeff`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.coeff_succ`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.continuous_nbessel`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel_deriv`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_contiguous`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_ode`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_pos_near_zero`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.nbessel_zero`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.summable_nbessel`
- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Series.summable_norm_series`
- Dependency: [D5/S3/Analytic/BesselRedheffer/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/KummerRatio/Series](../KummerRatio/Series.md)
