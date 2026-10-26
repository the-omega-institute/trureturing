# The hyperbolic cotangent remainder

## Abstract

A Bernoulli remainder and two consecutive derivative signs.

**Definition 1.1 (The remainder).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/Defs.p`

*Formalization.* `D5/S3/Analytic/CothBernoulliDegree/Defs.p` (`✓ std3`).

*Citation.* L. Zhu (2020). *Completely monotonic integer degrees for a class of special functions*. DOI: [10.3934/math.2020224](https://doi.org/10.3934/math.2020224). URL: <https://www.aimspress.com/article/doi/10.3934/math.2020224>.

*Commentary.*

For a natural n, subtract from cosh(t)/sinh(t)/t the sum over k from zero through n of 2^(2k) B_(2k) t^(2k-2)/(2k)!. The powers of t in this finite sum are integer powers. Only even Bernoulli indices occur.

**Definition 1.2 (The weighted remainder).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/Defs.P`

*Formalization.* `D5/S3/Analytic/CothBernoulliDegree/Defs.P` (`✓ std3`).

*Citation.* L. Zhu (2020). *Completely monotonic integer degrees for a class of special functions*. DOI: [10.3934/math.2020224](https://doi.org/10.3934/math.2020224). URL: <https://www.aimspress.com/article/doi/10.3934/math.2020224>.

*Commentary.*

For natural m and n, P(m,n,t) is (-1)^n times t^m times the remainder p(n,t).

**Definition 1.3 (Two consecutive derivative orders).**

Lean statement: `D5/S3/Analytic/CothBernoulliDegree/Defs.claim`

*Formalization.* `D5/S3/Analytic/CothBernoulliDegree/Defs.claim` (`✓ std3`).

*Citation.* L. Zhu (2020). *Completely monotonic integer degrees for a class of special functions*. DOI: [10.3934/math.2020224](https://doi.org/10.3934/math.2020224). URL: <https://www.aimspress.com/article/doi/10.3934/math.2020224>.

*Commentary.*

For every natural m at least one and natural n at least two, the derivative of P(m,n) of order m+2n-2 is strictly positive at every positive real t. The derivative of order m+2n-1 is not strictly positive at every positive real t.

## References

- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/Defs.P`
- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/Defs.claim`
- Truth anchor: `D5/S3/Analytic/CothBernoulliDegree/Defs.p`
