# The quarter-digamma resolvent on the full real line

## Abstract

The actual quarter-digamma residual has an exact positive rational L1 expansion.

**Theorem 1.1 (Actual L1 integrability, exact norm series and the bare increment sum).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>0, put c_n=n+1/4 and W(x)=Re(psi(1/4+i*x))-Re(psi(1/4)). On full real-line Lebesgue measure, W(x)/(x^2+a^2) is integrable. The nonnegative rational layer x^2/[c_n*(x^2+c_n^2)*(x^2+a^2)] is integrable and has norm integral pi/[c_n*(a+c_n)]. These exact norms form a summable series, and their sum equals the norm integral of the actual resolvent.

The pointwise bare series sum of 1/c_n-c_n/(x^2+c_n^2) is exactly W(x). This follows from the existing public DigammaSeries.hasSum_digamma_series at -3/4+i*x and -3/4: take real parts of each convergent series, subtract to cancel the harmonic term, and apply the digamma recurrence. GammaMu supplies the real-term formula and the quarter-line pole avoidance; an integer shift gives the required -3/4-line membership.

Partial fractions give the exact layer integral when a differs from c_n. At resonance a=c_n, a sequence of nonresonant parameters and a common integrable Cauchy majorant justify dominated convergence. This includes the actual layer a=c_n=5/4, whose norm integral is 8*pi/25. A shifted p-series bounds the layer norms. Tonelli then proves the actual resolvent's L1 integrability and the exact norm sum.

At a=5/4 the literal residual is an L1 Fourier multiplier. For an actual L1 half-line input, the reflected unitary Fourier cross calculation first proves absolute product integrability and then applies Fubini, with kernel factor 1/(2*pi). The final bare HasSum also supplies the finite spectral monotone-convergence calculation for this same W. These uses retain their actual integrability and weighted domain assumptions. The residual theorem supplies neither a complete Gamma energy identity nor RH positivity.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series`
