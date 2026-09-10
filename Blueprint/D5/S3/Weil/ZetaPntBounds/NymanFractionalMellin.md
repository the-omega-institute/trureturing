# Real Fractional-Part Mellin Identity

## Abstract

Real Fractional-Part Mellin Identity.

**Theorem 1.1 (Fractional Mellin base identity).**

$$\forall s\in\mathbb{C},0<\Re s\land s\neq1\Rightarrow\int_{0}^{1}\operatorname{fract}(\frac{1}{x})x^{s-1}\,dx=\frac{1}{s-1}-\frac{\zeta(s)}{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.bd_mellin_base_case_proved` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

For real part of s greater than zero and s different from one, the exact selected upstream proof continues the floor-series identity using analyticity and connectedness. Connectedness reuses ZetaBoundsUpper.isPathConnected_aux.

**Theorem 1.2 (Integrability for every real parameter).**

$$\forall \theta\in\mathbb{R},s\in\mathbb{C},0<\Re s\Rightarrow\operatorname{IntegrableOn}((x\mapsto\operatorname{fract}(\theta/x)x^{s-1}),(0,1),\operatorname{volume})$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_integrableOn` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

For every real theta and real part of s greater than zero, the actual integrand is integrable on Ioo zero one. Bounded measurable fractional part is dominated by an integrable complex power; there is no restriction on theta.

**Theorem 1.3 (Real-parameter scaling).**

$$\forall \theta\in\mathbb{R},s\in\mathbb{C},0<\theta\le1\land0<\Re s\land s\neq1\Rightarrow\int_{0}^{1}\operatorname{fract}(\frac{\theta}{x})x^{s-1}\,dx=\theta^{s}\int_{0}^{1}\operatorname{fract}(\frac{1}{x})x^{s-1}\,dx+\frac{\theta-\theta^{s}}{s-1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_scaling` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

For zero less than theta at most one, real part of s positive, and s different from one, substitute the real scale one over theta, split the integral at one, and integrate the tail using fract of one over u equals one over u for u greater than one. The case theta equals one and null endpoints are included.

**Theorem 1.4 (Literal E9).**

$$\forall \theta\in\mathbb{R},s\in\mathbb{C},0<\theta\le1\land0<\Re s<1\Rightarrow\int_{0}^{1}\operatorname{fract}(\frac{\theta}{x})x^{s-1}\,dx=\frac{\theta}{s-1}-\frac{\theta^{s}\zeta(s)}{s}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_eq_zeta` (`✓ std3`). ∎

*Citation.* Jason Robert Gochanour (2026). *Prime Cathedral fractional-part Mellin identities*. URL: <https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral>.

*Commentary.*

For every real theta with zero less than theta at most one, and every complex s with real part strictly between zero and one, the actual fractional-part integral equals theta divided by s minus one minus theta to the complex power s times riemannZeta s divided by s. Positive real bases use mathlib's principal complex power, agreeing with the real logarithm. The separate unit-interval functional, Lp source vectors, and separating functional are not constructed here.

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.bd_mellin_base_case_proved`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_eq_zeta`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_integrableOn`
- Truth anchor: `D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin.fractionalMellin_scaling`
- Dependency: [D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries](NymanMellinFloorSeries.md)
