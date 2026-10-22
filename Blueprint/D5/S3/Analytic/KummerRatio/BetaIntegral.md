# Beta integral representation

## Abstract

Beta moments and integral formulas for the Kummer function.

**Theorem 1.1 (Real beta moments).**

Lean statement: `D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real p and q, the integral over the unit interval of t raised to p minus one times one minus t raised to q minus one equals Gamma(p) Gamma(q) divided by Gamma(p+q). The complex beta identity transfers to this real integral because both bases are nonnegative on the integration interval.

**Theorem 1.2 (Integrable beta weight).**

Lean statement: `D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive shape parameters, the real beta weight is integrable over the unit interval. This follows by taking the real part of the convergent complex beta integrand.

**Theorem 1.3 (The beta representation of Kummer's function).**

Lean statement: `D5/S3/Analytic/KummerRatio/BetaIntegral.kummer_eq_betaIntegral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/BetaIntegral.kummer_eq_betaIntegral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When zero is less than s and s is less than c, Kummer's function M(s;c;x) is the integral of exp(xt) against the beta weight t^(s-1)(1-t)^(c-s-1), multiplied by Gamma(c)/(Gamma(s) Gamma(c-s)). The exponential series is integrated term by term. The terms in absolute value are bounded by the beta weight multiplied by |x|^n/n!, whose sum is integrable. The Gamma and ascending Pochhammer identity identifies each resulting beta moment with the defining Kummer coefficient.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/BetaIntegral.integral_beta`
- Truth anchor: `D5/S3/Analytic/KummerRatio/BetaIntegral.intervalIntegrable_beta`
- Truth anchor: `D5/S3/Analytic/KummerRatio/BetaIntegral.kummer_eq_betaIntegral`
- Dependency: [D5/S3/Analytic/KummerRatio/Defs](Defs.md)
