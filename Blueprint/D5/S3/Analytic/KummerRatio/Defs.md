# The upper parameter ratio

## Abstract

Kummer series and ratios with shifted upper parameters.

**Definition 1.1 (The series coefficient).**

Lean statement: `D5/S3/Analytic/KummerRatio/Defs.kummerCoeff`

*Formalization.* `D5/S3/Analytic/KummerRatio/Defs.kummerCoeff` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2010). *Log-convexity and log-concavity of hypergeometric-like functions*. DOI: [10.1016/j.jmaa.2009.10.057](https://doi.org/10.1016/j.jmaa.2009.10.057). URL: <https://arxiv.org/abs/0902.3073>.

*Commentary.*

For real s and c and a natural n, the coefficient is the rising factorial of s of order n divided by the rising factorial of c of order n and by n factorial.

**Definition 1.2 (Kummer's function).**

Lean statement: `D5/S3/Analytic/KummerRatio/Defs.kummer`

*Formalization.* `D5/S3/Analytic/KummerRatio/Defs.kummer` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2010). *Log-convexity and log-concavity of hypergeometric-like functions*. DOI: [10.1016/j.jmaa.2009.10.057](https://doi.org/10.1016/j.jmaa.2009.10.057). URL: <https://arxiv.org/abs/0902.3073>.

*Commentary.*

The function M(s;c;x) is the sum over all natural n of the coefficient times x to the power n.

**Definition 1.3 (The shifted upper parameter ratio).**

Lean statement: `D5/S3/Analytic/KummerRatio/Defs.ratio`

*Formalization.* `D5/S3/Analytic/KummerRatio/Defs.ratio` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2010). *Log-convexity and log-concavity of hypergeometric-like functions*. DOI: [10.1016/j.jmaa.2009.10.057](https://doi.org/10.1016/j.jmaa.2009.10.057). URL: <https://arxiv.org/abs/0902.3073>.

*Commentary.*

The ratio is M(b+delta;c;x) M(a;c;x) divided by M(a+delta;c;x) M(b;c;x).

**Definition 1.4 (Monotonicity and exact ranges).**

Lean statement: `D5/S3/Analytic/KummerRatio/Defs.claim`

*Formalization.* `D5/S3/Analytic/KummerRatio/Defs.claim` (`✓ std3`).

*Citation.* D. Karp and S. M. Sitnik (2010). *Log-convexity and log-concavity of hypergeometric-like functions*. DOI: [10.1016/j.jmaa.2009.10.057](https://doi.org/10.1016/j.jmaa.2009.10.057). URL: <https://arxiv.org/abs/0902.3073>.

*Commentary.*

For c and delta positive and 0<a<b, the ratio is strictly decreasing on the positive ray and has image (Gamma(a+delta) Gamma(b)/(Gamma(b+delta) Gamma(a)),1). For a<b<c-delta, it is strictly increasing on the negative ray and has image (Gamma(c-a-delta) Gamma(c-b)/(Gamma(c-b-delta) Gamma(c-a)),1).

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/Defs.claim`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Defs.kummer`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Defs.kummerCoeff`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Defs.ratio`
