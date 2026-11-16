# Positive ratios eliminate a linear exponent

## Abstract

The magnitude and continuous real-tail phase of an exponential ratio determine its linear term.

**Theorem 1.1 (The linear complex exponent vanishes).**

Lean statement: `D5/S3/Analytic/Asymptotics/PositiveSubexponentialRatio.linear_exponent_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/PositiveSubexponentialRatio.linear_exponent_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a,b be arbitrary complex numbers and p,q real functions eventually strictly positive on the full real tail. If log(p(x))/x and log(q(x))/x tend to zero, and exp(a*x+b)*p(x)/q(x) tends to one as real x tends to positive infinity, then a=0. Taking the logarithm of the norm forces the real part to vanish. Translation invariance of the normalized phase limit, followed by a half-turn contradiction, forces the imaginary part to vanish. This result is consumed by SparseQuartetProduct.fast_ratio_rigidity.

The conclusion concerns a, not the chosen logarithm b. It uses eventual positivity and a full real-tail limit, not integer samples. It makes no actual-zeta, RH, minimal-type or literature-novelty claim. This is a general asymptotic theorem, not enumeration, numerical reduction, checker infrastructure or a certified finite instance; utility is none. The proof uses Mathlib logarithm, exponential, limit and trigonometric identities.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/PositiveSubexponentialRatio.linear_exponent_eq_zero`
