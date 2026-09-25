# Real-time Edgeworth expansion for two Poisson jumps

## Abstract

Independent Poisson jumps with irrational ratio satisfy a uniform first Edgeworth expansion, a fixed-width local limit, and uniform atom decay.

**Theorem 1.1 (Finite-frequency smoothing for a signed density).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.generic_finite_smoothing`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.generic_finite_smoothing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Let P be any probability measure on the real line, and let q be an integrable real comparison density bounded in absolute value by A. Assume its lower-half-line integral is Lipschitz with constant A. There is a universal positive H such that the distribution-function error is bounded by twice a finite Fourier integral plus 4AH divided by the bandwidth.

Convolution with a squared-sinc probability density cuts off Fourier frequencies. Monotonicity of the actual distribution function and the Lipschitz property of the signed comparison absorb the remaining tail discrepancy.

**Theorem 1.2 (A Gaussian envelope on a growing frequency interval).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.low_frequency_integral_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.low_frequency_integral_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Write V for p times a squared plus q times b squared, and use the raw cubic and quartic jump moments. On a sufficiently small fixed raw-frequency interval, the cubic and quartic exponent terms are absorbed by one quarter of the quadratic Gaussian exponent.

After rescaling by square-root time w, the error divided by frequency is bounded by a Gaussian times a polynomial of degrees three, five, and seven, divided by w squared. This integrable envelope makes w times the low-frequency integral tend to zero.

**Theorem 1.3 (The full moving-cutoff Fourier error vanishes).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.symmetric_cutoff_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.symmetric_cutoff_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Assume p and q are positive, b is nonzero, and a divided by b is irrational. For every fixed positive C, w times the characteristic-function error integral over the symmetric interval from minus Cw to Cw tends to zero. The comparison uses variance V and the raw third jump moment.

Irrationality prevents both cosine terms from attaining one at a nonzero frequency. Compactness therefore gives a positive damping gap on each fixed annulus. The low-frequency Gaussian estimate, this annular gap, and an integrable Gaussian correction tail control the whole interval.

**Theorem 1.4 (Uniform Edgeworth expansion, local limits, and atom decay).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.result`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Take independent Poisson counts with means lambda times p and lambda times q. The weighted sum has mean lambda times (pa+qb) and variance lambda times (p a squared+q b squared). Standardize by that exact mean and variance. The correction coefficient uses p a cubed+q b cubed, the raw third jump moment.

For every positive error tolerance, all sufficiently large real lambda satisfy the first Edgeworth estimate uniformly over every real threshold. Choose the raw-frequency cutoff first and then let square-root time grow; finite signed smoothing and the moving-cutoff estimate give the limit.

For every fixed positive width h, the probability that the unstandardized weighted sum lies in (y,y+h], multiplied by square-root lambda, converges uniformly in y to h divided by the square root of V times the standard Gaussian density at the standardized left endpoint. Uniform continuity of the Gaussian density and its correction controls the difference of the two distribution functions.

The mass at every standardized score, multiplied by square-root lambda, tends uniformly to zero. The comparison distribution function is continuous, so its uniform error bounds the jump of the actual distribution function. All three conclusions use arbitrary fixed positive rates and arbitrary real jump sizes subject to the nonzero denominator and irrational-ratio hypotheses.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.generic_finite_smoothing`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.low_frequency_integral_vanishes`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.result`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworth.symmetric_cutoff_vanishes`
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers](StatLeanFourierSuppliers.md)
