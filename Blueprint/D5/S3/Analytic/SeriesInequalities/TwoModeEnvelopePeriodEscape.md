# Two-Mode Envelope Period Escape

## Abstract

A full period defeats an opposite-phase two-mode contact throughout a real parameter range.

**Definition 1.1 (A damped mode and its lag).**

$$\operatorname{mode}\left(b, g, v\right)=\exp(-(1-b)v)(\operatorname{c}\left(b, g\right)\operatorname{cos}\left(gv\right)-\operatorname{d}\left(b, g\right)\sin(gv))-\operatorname{a}\left(b, g\right)\exp(-v)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set alpha=1-b, Da(b,g)=g^2+alpha^2 and Db(b,g)=g^2+b^2. The real coefficients are c(b,g)=2(alpha/Da+b/Db), d(b,g)=2g(2b-1)/(Da Db) and a(b,g)=2b/Db. For rho=b+ig, the complex coefficient -2/(rho(rho-1)) has real part c and imaginary part d. Thus the oscillatory term uses c cos(gv)-d sin(gv); the lag uses exp(-v).

**Definition 1.2 (The opposite-phase profile).**

$$\operatorname{profile}\left(b, g_{1}, g_{2}, v\right)=\operatorname{mode}\left(b, g_{1}, v\right)-\operatorname{mode}\left(b, g_{2}, v\right)$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtracting the second mode implements the relative phase pi, including the difference of the lag coefficients. The same real part b and time coordinate v are used for both modes.

**Theorem 1.3 (The first period strictly beats the origin).**

$$\forall b,g_{1},g_{2} \in \mathbb{R}, (\frac{7}{10}\le b\land b<1\land 14\le g_{1}\land g_{1}<g_{2}) \implies \operatorname{profile}\left(b, g_{1}, g_{2}, 0\right)<\operatorname{profile}\left(b, g_{1}, g_{2}, \frac{2\pi}{g_{1}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All parameters are real: 7/10<=b<1 and 14<=g1<g2. At v=2pi/g1 the first mode returns to its initial phase. Exponential bounds and the denominator comparison give a strict difference between the same-phase increments. When g2<=3g1/2, the second-mode sine is nonnegative and cannot erase that gain. For larger g2, the possible phase gain is at most g2^(-4), which is smaller than the first-period increment difference. Consequently the origin cannot dominate this profile at all real times. The strict margin depends on the parameters. The conclusion covers this profile and this real-part range; it does not identify a profile limit of actual ordinary-integer Robin sources, establish their phase realization, or bound the remaining zeta zero modes.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.mode`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.profile`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/TwoModeEnvelopePeriodEscape.result`
