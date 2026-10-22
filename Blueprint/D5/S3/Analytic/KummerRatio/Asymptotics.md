# Gamma-normalized Kummer asymptotics

## Abstract

The leading positive-real asymptotic of the Kummer series.

**Theorem 1.1 (The exact leading coefficient).**

Lean statement: `D5/S3/Analytic/KummerRatio/Asymptotics.tendsto_kummer_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Asymptotics.tendsto_kummer_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive upper parameter s and positive lower parameter c, the quantity exp(-x) x^(c-s) M(s;c;x) tends to Gamma(c)/Gamma(s) as x tends to positive infinity.

When s is less than c, the beta integral represents the Kummer series. The normalized integral concentrates at the right endpoint, and its limit is Gamma(c-s). Multiplication by the beta normalization gives the stated coefficient.

For all other positive parameters, the contiguous relation expresses the normalized function as the sum of two normalized functions with a larger lower parameter. The first is multiplied by 1/x and tends to zero. The coefficient of the second reduces to Gamma(c)/Gamma(s) by the Gamma recurrence. Induction on a natural upper bound for s-c reaches the integral case.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/Asymptotics.tendsto_kummer_atTop`
- Dependency: [D5/S3/Analytic/KummerRatio/BetaAsymptotics](BetaAsymptotics.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](BetaIntegral.md)
- Dependency: [D5/S3/Analytic/KummerRatio/Series](Series.md)
