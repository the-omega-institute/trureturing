# Karp-Zhang Quadratic Truncations

## Abstract

Two quadratic truncations of the Karp-Zhang series have nonnegative generalized Turan coefficients for every nonnegative real pair of shifts.

The targets are r2 and r3 of issue #5969, from Dmitrii Karp and Yi Zhang, Log-concavity and log-convexity of series containing multiple Pochhammer symbols, Fractional Calculus and Applied Analysis 27 (2024), 458-486, DOI 10.1007/s13540-023-00238-0. The results concern only the specified truncations of Conjectures 1 and 2, not either full series conjecture.

**Definition 1.1 (The two-term r = 3 polynomial).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r2Polynomial`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r2Polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rising factorial is Mathlib's ascending Pochhammer polynomial evaluated at t. Only indices 1 and 2 are retained, with denominators 2! and 5!. The two weights can be any nonnegative real numbers.

**Definition 1.2 (The truncation at k = 2).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r3Polynomial`

*Formalization.* `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r3Polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The constant, linear and quadratic coefficients are respectively h0, h1*t and h2*t*(t+3)/2. The last expression is the k=2 Pochhammer quotient in the source series; no integer restriction is placed on t.

**Theorem 1.3 (Conjecture 1 for the two-term truncation).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r2_coeff_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r2_coeff_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative weights c1,c2, positive mu and arbitrary nonnegative real alpha and beta, every coefficient of F(mu+alpha)*F(mu+beta)-F(mu)*F(mu+alpha+beta) is nonnegative. The equal-index terms follow by factorwise comparison. The mixed (3,6) term is alpha*beta*(alpha+beta+2*mu+8) times a polynomial with positive coefficients in mu, alpha+beta, alpha*beta and (alpha-beta)^2; the identity is checked by the Lean kernel.

**Theorem 1.4 (Conjecture 2 for three terms and real shifts).**

Lean statement: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r3_coeff_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r3_coeff_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume h0,h1,h2 are nonnegative, h1^2 >= h0*h2, and mu is positive. For arbitrary nonnegative real alpha and beta, the degree-two Turan coefficient is alpha*beta*(h1^2-h0*h2). The degree-three coefficient is h1*h2*alpha*beta*(alpha+beta+2*mu+6)/2. The degree-four coefficient is h2^2*alpha*beta/4 times a polynomial with positive coefficients. All other coefficients vanish. The shifts are arbitrary nonnegative reals, extending the integer-shift scope of the paper's Theorem 3 for this truncation.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r2Polynomial`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r2_coeff_nonneg`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r3Polynomial`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/KarpQuadraticTruncations.r3_coeff_nonneg`
