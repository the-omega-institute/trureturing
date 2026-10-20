# The logarithmic Fourier tail

## Abstract

The actual shifted-logarithmic Fourier tail has an exact improper integral and a uniform positive-cutoff budget.

For a real cutoff R>0 integrate (1+log(1+t))/t^2 on the full half-line t>R. The shift inside the logarithm is retained. This is the scalar high-frequency integral in the same-window logarithmic Fourier approximation, independently of a test function, numerical trial, or arithmetic form.

**Theorem 1.1 (Every positive-cutoff tail is integrable).**

Lean statement: `D5/S3/Analytic/Fourier/LogarithmicTail.integrableOn_logarithmic_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/LogarithmicTail.integrableOn_logarithmic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonnegative actual integrand is integrable on (R,infinity) for every R>0. An explicit primitive is -(1+log(1+t))/t-(log(1+t)-log(t)). Its derivative and limit zero at infinity are proved before the improper fundamental theorem is applied. No integrability or endpoint value is assumed.

**Theorem 1.2 (The exact tail includes its endpoint logarithm).**

Lean statement: `D5/S3/Analytic/Fourier/LogarithmicTail.integral_logarithmic_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/LogarithmicTail.integral_logarithmic_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral equals (1+log(1+R))/R+log(1+1/R). The logarithmic difference in the primitive is converted to log(1+1/R) using the positive ratio (1+R)/R. Dropping this correction would give an incorrect exact identity. The unshifted log(t) tail already in QuotientIntegralBudget is a distinct integrand; that arithmetic module is not imported or re-proved.

**Theorem 1.3 (One explicit budget covers every positive cutoff).**

Lean statement: `D5/S3/Analytic/Fourier/LogarithmicTail.integral_logarithmic_tail_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Fourier/LogarithmicTail.integral_logarithmic_tail_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same integral is at most (2+log(1+R))/R. The elementary bound log(1+1/R)<=1/R pays the endpoint correction. This holds for all R>0, including the R>=1 range used in a Fourier split. It does not supply the Fourier integration-by-parts estimate, a form-domain identification, an actual signed Weil trial, or a Riemann-hypothesis conclusion.

## References

- Truth anchor: `D5/S3/Analytic/Fourier/LogarithmicTail.integrableOn_logarithmic_tail`
- Truth anchor: `D5/S3/Analytic/Fourier/LogarithmicTail.integral_logarithmic_tail`
- Truth anchor: `D5/S3/Analytic/Fourier/LogarithmicTail.integral_logarithmic_tail_le`
