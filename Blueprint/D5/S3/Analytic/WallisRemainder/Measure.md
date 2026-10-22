# Spectral probability laws

## Abstract

An odd spectral mixture and its size-biased probability law.

**Theorem 1.1 (The Stieltjes representation).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.r_eq_stieltjes`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.r_eq_stieltjes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive x, minus log B(x) is x/8 times the integral of 1/(x squared+v) under P. The hyperbolic partial fractions decompose the Laplace kernel into positive spectral terms. Their integral norms have a summable bound given by the spectral weights divided by 8x. Interchanging the sum and integral and scaling the exponential variable identifies each term with its spectral probability component.

**Theorem 1.2 (Hyperbolic partial fractions).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.tanh_div_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.tanh_div_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive u, tanh(u)/u is the sum, over natural n, of 8/(pi squared times (2n+1) squared plus 4u squared). The cotangent expansion on the positive imaginary axis gives the hyperbolic cotangent expansion. Splitting its even and odd terms gives the formula.

**Theorem 1.3 (Spectral normalization).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.hasSum_spectralWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.hasSum_spectralWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive weights 8/(pi squared times (2n+1) squared), for natural n, sum to one.

**Theorem 1.4 (Positive support of the spectral law).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.P_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.P_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The law P is the mixture, with the normalized odd spectral weights, of a(n)U squared, where U has density exp(-u) on the positive ray and a(n)=1/(4 pi squared times (2n+1) squared). It assigns full measure to strictly positive values.

**Theorem 1.5 (Finite first moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_id`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_id` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity function is integrable with respect to P.

**Theorem 1.6 (Finite second moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square function is integrable with respect to P.

**Theorem 1.7 (Finite third moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_cube`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cube function is integrable with respect to P.

**Theorem 1.8 (The first spectral moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integral_P_id`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integral_P_id` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mean of P is 1/24.

**Theorem 1.9 (The second spectral moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integral_P_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integral_P_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second moment of P is 1/80.

**Theorem 1.10 (The third spectral moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integral_P_cube`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integral_P_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The third moment of P is 17/1792. Gamma integrals evaluate each exponential component; the odd sums of reciprocal even powers give the exact mixture moments.

**Theorem 1.11 (Positive support after size biasing).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.Q_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.Q_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The probability law Q, with density 24v relative to P, assigns full measure to strictly positive values.

**Theorem 1.12 (Integration after size biasing).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integral_Q`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integral_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real function f on the real line, its integral under Q equals 24 times the integral of v times f(v) under P.

**Theorem 1.13 (Finite size-biased first moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integrable_Q_id`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integrable_Q_id` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity function is integrable with respect to Q.

**Theorem 1.14 (Finite size-biased second moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integrable_Q_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integrable_Q_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square function is integrable with respect to Q.

**Theorem 1.15 (The size-biased mean).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integral_Q_id`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integral_Q_id` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mean of Q is 3/10.

**Theorem 1.16 (The size-biased second moment).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.integral_Q_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.integral_Q_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second moment of Q is 51/224.

**Theorem 1.17 (The spectral variance).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.variance_P`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.variance_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variance of the identity function under P is 31/2880.

**Theorem 1.18 (The size-biased variance).**

Lean statement: `D5/S3/Analytic/WallisRemainder/Measure.variance_Q`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/WallisRemainder/Measure.variance_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The variance of the identity function under Q is 771/5600.

## References

- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.P_pos`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.Q_pos`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.hasSum_spectralWeight`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_cube`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_id`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integrable_P_sq`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integrable_Q_id`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integrable_Q_sq`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integral_P_cube`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integral_P_id`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integral_P_sq`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integral_Q`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integral_Q_id`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.integral_Q_sq`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.r_eq_stieltjes`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.tanh_div_hasSum`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.variance_P`
- Truth anchor: `D5/S3/Analytic/WallisRemainder/Measure.variance_Q`
- Dependency: [D5/S3/Analytic/WallisRemainder/Laplace](Laplace.md)
- Dependency: [D5/S3/Analytic/WallisRemainder/Stieltjes](Stieltjes.md)
