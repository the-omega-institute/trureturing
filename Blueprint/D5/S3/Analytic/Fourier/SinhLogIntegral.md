# The hyperbolic sine density

## Abstract

Logarithmic cosine integrals for normalized hyperbolic sine.

**Theorem 1.1 (Comparison across scales).**

Lean statement: `D5/S3/Analytic/Fourier/SinhLogIntegral.h_scale_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/SinhLogIntegral.h_scale_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and s and b at least a, define h(a,s)=1/(exp(pi s/a)-1). Then h(b,s) is at least (b/a) h(a,s). Convexity of the real exponential between zero and pi s/a gives the denominator comparison; all denominators are strictly positive.

**Theorem 1.2 (Integrability of the weighted density).**

Lean statement: `D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_levyWeight`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_levyWeight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive a, the function min(1,s squared) h(a,s)/s is integrable on the positive half-line. The estimate exp(x)-1 at least x bounds the integrand near zero by a/pi. Beyond one the density is bounded by a constant times exp(-pi s/a), which is integrable.

**Theorem 1.3 (Absolute integrability of cosine deficits).**

Lean statement: `D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_logIntegrand`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_logIntegrand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and every real t, (1-cos(ts)) h(a,s)/s is integrable on the positive half-line. The cosine deficit is nonnegative and bounded by (t squared plus two) times min(1,s squared). This supplies the absolute integrability needed for linear combinations of the logarithmic densities.

**Theorem 1.4 (The logarithmic integral formula).**

Lean statement: `D5/S3/Analytic/Fourier/SinhLogIntegral.log_E_eq_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/SinhLogIntegral.log_E_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, let E(a,t)=sinh(at)/(at) away from zero and E(a,0)=1. For every real t, log E(a,t) equals twice the integral of (1-cos(ts)) h(a,s)/s over positive s. The formula includes t=0.

The complex Euler sine product on the imaginary axis gives the product of 1+(at) squared divided by pi squared times n squared. Positivity permits taking logarithms. Fubini's theorem and the half-line integral of a complex exponential give the elementary formula log(1+t squared/b squared)=2 integral (1-cos(ts)) exp(-bs)/s for b positive. Summing these identities uses the geometric expansion of h and the integrable density bound. This is an identity of real Lebesgue integrals; it does not impose integrability of h itself at zero.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/SinhLogIntegral.h_scale_le`
- Truth anchor: `D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_levyWeight`
- Truth anchor: `D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_logIntegrand`
- Truth anchor: `D5/S3/Analytic/Fourier/SinhLogIntegral.log_E_eq_integral`
