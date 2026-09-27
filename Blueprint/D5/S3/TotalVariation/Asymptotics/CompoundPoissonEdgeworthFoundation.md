# Finite smoothing and low-frequency Poisson decay

## Abstract

Finite signed smoothing and a Gaussian envelope control the low-frequency error of two-jump Poisson laws.

**Theorem 1.1 (Finite-frequency smoothing for a signed density).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.generic_finite_smoothing`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.generic_finite_smoothing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Let P be any probability measure on the real line, and let q be an integrable real comparison density bounded in absolute value by A. Assume its lower-half-line integral is Lipschitz with constant A. There is a universal positive H such that, for every positive bandwidth on whose frequency interval the weighted Fourier difference is integrable, the distribution-function error is bounded by twice that Fourier integral plus 4AH divided by the bandwidth.

Convolution with a squared-sinc probability density cuts off Fourier frequencies. Monotonicity of the actual distribution function and the Lipschitz property of the signed comparison absorb the remaining tail discrepancy.

**Theorem 1.2 (A Gaussian envelope on a growing frequency interval).**

Lean statement: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.low_frequency_integral_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.low_frequency_integral_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

Let p, q, a, b, and delta be real numbers. Assume p >= 0 and q >= 0; write V = p×a^2 + q×b^2 and assume V > 0. Assume delta >= 0, delta×abs(a) <= 1, delta×abs(b) <= 1, and abs(p×a^3 + q×b^3)×delta/6 + (p×a^4 + q×b^4)×delta^2 <= V/4. On the rescaled interval 0 <= u <= delta×w for w >= 1, these hypotheses bound the cubic and quartic exponent terms by V×u^2/4, leaving the Gaussian envelope exp(-V×u^2/4).

After rescaling by square-root time w, the error divided by frequency is bounded by a Gaussian times a polynomial of degrees three, five, and seven, divided by w squared. This integrable envelope makes w times the low-frequency integral tend to zero.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.generic_finite_smoothing`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.low_frequency_integral_vanishes`
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers](StatLeanFourierSuppliers.md)
