# Gamma ratios and differentiated series

## Abstract

Entire real series and signed derivatives for the Kilbas-Saigo function.

**Definition 1.1 (The affine Gamma ratio).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.phi`

*Formalization.* `D5/S3/Analytic/KilbasSaigo/Series.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With a=1+alpha(l-m) and b=alpha m, phi(s)=Gamma(a+b s+alpha)/Gamma(a+b s).

**Definition 1.2 (Derivative coefficients).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.gCoeff`

*Formalization.* `D5/S3/Analytic/KilbasSaigo/Series.gCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient d(k,n) is (n+k)!/n! times the coefficient c(n+k) of the defining series.

**Definition 1.3 (Signed derivative series).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.g`

*Formalization.* `D5/S3/Analytic/KilbasSaigo/Series.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The series g(k,x) is the sum of d(k,n)(-x)^n over natural n.

**Theorem 1.4 (Positive initial argument).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.base_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.base_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The assumptions alpha>0 and l>m-1/alpha imply a=1+alpha(l-m)>0.

**Theorem 1.5 (Positive Gamma ratios).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.phi_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.phi_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha>0, m>0, l>m-1/alpha and s>=0, phi(s)>0, since both Gamma arguments are positive.

**Theorem 1.6 (Coefficient recurrence).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.ksCoeff_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.ksCoeff_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product defining c(n+1) equals c(n)/phi(n+1). This identity holds for all real parameters.

**Theorem 1.7 (Positive coefficients).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.ksCoeff_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.ksCoeff_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha>0, m>0 and l>m-1/alpha, every coefficient c(n) is strictly positive.

**Theorem 1.8 (A beta integral for the reciprocal ratio).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.inv_phi_eq_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.inv_phi_eq_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For admissible parameters and s>=0, 1/phi(s) equals the integral from zero to one of r^(a+b s-1)(1-r)^(alpha-1), divided by Gamma(alpha).

**Theorem 1.9 (Decay of reciprocal Gamma ratios).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.tendsto_inv_phi`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.tendsto_inv_phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha>0, m>0 and l>m-1/alpha, 1/phi(n) tends to zero as n tends to infinity. The beta density with exponent a-1 dominates all densities in the sequence; at every interior point the exponent tends to infinity.

**Theorem 1.10 (Derivative coefficient recurrence).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.gCoeff_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.gCoeff_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio recurrence for d(k,n+1) is ((n+k+1)/(n+1))/phi(n+k+1) times d(k,n).

**Theorem 1.11 (The differentiated coefficient).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.gCoeff_step`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.gCoeff_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying d(k,n+1) by n+1 gives d(k+1,n).

**Theorem 1.12 (Convergence of derivative series).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.summable_gCoeff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.summable_gCoeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha>0, m>0 and l>m-1/alpha, each derivative coefficient series converges absolutely at every real argument. Its successive multiplier tends to zero, so a geometric majorant applies to its tail.

**Theorem 1.13 (Convergence of the defining series).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.summable_kilbasSaigo`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.summable_kilbasSaigo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The defining Kilbas-Saigo series converges for every real argument under alpha>0, m>0 and l>m-1/alpha.

**Theorem 1.14 (Initial derivative values).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.g_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.g_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value g(k,0) is k! c(k), for every real parameter triple.

**Theorem 1.15 (Positive initial derivatives).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.g_zero_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.g_zero_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under alpha>0, m>0 and l>m-1/alpha, each g(k,0) is strictly positive.

**Theorem 1.16 (The original series as order zero).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.kilbasSaigo_neg_eq_g0`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.kilbasSaigo_neg_eq_g0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real parameter triple and x, the defining function at -x is g(0,x).

**Theorem 1.17 (Differentiating the series).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.hasDerivAt_g`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.hasDerivAt_g` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For alpha>0, m>0 and l>m-1/alpha, g(k,x) has derivative -g(k+1,x) at every real x. On each bounded interval, the next derivative series supplies a summable uniform bound on monomial derivatives.

**Theorem 1.18 (Continuity of all derivative series).**

Lean statement: `D5/S3/Analytic/KilbasSaigo/Series.continuous_g`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KilbasSaigo/Series.continuous_g` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each g(k,.) is continuous on the whole real line under the same parameter assumptions.

## References

- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.base_pos`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.continuous_g`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.g`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.gCoeff`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.gCoeff_step`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.gCoeff_succ`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.g_zero`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.g_zero_pos`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.hasDerivAt_g`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.inv_phi_eq_beta`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.kilbasSaigo_neg_eq_g0`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.ksCoeff_pos`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.ksCoeff_succ`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.phi`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.phi_pos`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.summable_gCoeff`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.summable_kilbasSaigo`
- Truth anchor: `D5/S3/Analytic/KilbasSaigo/Series.tendsto_inv_phi`
- Dependency: [D5/S3/Analytic/KilbasSaigo/Defs](Defs.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
