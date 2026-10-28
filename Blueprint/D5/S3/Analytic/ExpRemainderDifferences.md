# A negative third forward difference

## Abstract

Forward differences of consecutive exponential remainder ratios.

**Definition 1.1 (Exponential Taylor remainders).**

Lean statement: `D5/S3/Analytic/ExpRemainderDifferences.R`

*Formalization.* `D5/S3/Analytic/ExpRemainderDifferences.R` (`✓ std3`).

*Citation.* S. M. Sitnik (1993). *Inequalities for the exponential remainder of the Taylor series*. URL: <https://arxiv.org/abs/1608.08784>.

*Commentary.*

For each natural n and real x, R(n,x) is exp(x) minus the sum of x to the k divided by k factorial over k from zero through n. This is the remainder after the Taylor polynomial of degree n.

**Definition 1.2 (Consecutive remainder ratios).**

Lean statement: `D5/S3/Analytic/ExpRemainderDifferences.g`

*Formalization.* `D5/S3/Analytic/ExpRemainderDifferences.g` (`✓ std3`).

*Citation.* S. M. Sitnik (1993). *Inequalities for the exponential remainder of the Taylor series*. URL: <https://arxiv.org/abs/1608.08784>.

*Commentary.*

For each natural n and real x, g(n,x) is R(n-1,x) divided by R(n,x). The assertion below uses n at least one and positive x, so natural subtraction agrees with the preceding remainder index.

**Definition 1.3 (The universal nonnegativity assertion).**

Lean statement: `D5/S3/Analytic/ExpRemainderDifferences.claim`

*Formalization.* `D5/S3/Analytic/ExpRemainderDifferences.claim` (`✓ std3`).

*Citation.* S. M. Sitnik (1993). *Inequalities for the exponential remainder of the Taylor series*. URL: <https://arxiv.org/abs/1608.08784>.

*Commentary.*

Source, problem 11 of Sitnik's exponential remainder paper, PDF page 28: «11. Определим функцию при x > 0. gₙ(x) = Rₙ₋₁(x)/Rₙ(x). Исследовать, при каких k разности этой функции при любом фиксированном x неотрицательны ∆ᵏgₙ(x) > 0? Гипотеза: при любых k.» In English: define g(n,x) = R(n-1,x)/R(n,x) for x > 0; for which k are the differences of this function, at every fixed x, nonnegative; conjecture: for all k. The assertion here says that for every natural k and n at least one, and every positive real x, the k-fold iterate of Mathlib's forward difference operator fwdDiff with step one, applied to the sequence m mapped to g(m,x) and evaluated at n, is nonnegative. A negative value also contradicts the strict positivity printed in the source.

**Theorem 1.4 (The universal assertion is false).**

Lean statement: `D5/S3/Analytic/ExpRemainderDifferences.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExpRemainderDifferences.result` (`✓ std3`). ∎

*Resolves.* `Problems/sitnik-1993-exponential-remainder-differences` (refuted) by `D5/S3/Analytic/ExpRemainderDifferences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sitnik-1993-exponential-remainder-differences","declaration_gid":"D5/S3/Analytic/ExpRemainderDifferences.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. M. Sitnik (1993). *Inequalities for the exponential remainder of the Taylor series*. URL: <https://arxiv.org/abs/1608.08784>.

*Commentary.*

At order three, index one and argument one, the forward difference is strictly negative. Mathlib's binomial expansion expresses it as g(4,1) minus three times g(3,1) plus three times g(2,1) minus g(1,1). The five Taylor remainders are exp(1) minus 1, 2, 5/2, 8/3 and 65/24. The bounds 2.7182818283 < exp(1) < 2.7182818286 make every denominator positive and bound each ratio rationally; the bounds combine to a negative value. This contradicts universal nonnegativity.

## References

- Truth anchor: `D5/S3/Analytic/ExpRemainderDifferences.R`
- Truth anchor: `D5/S3/Analytic/ExpRemainderDifferences.claim`
- Truth anchor: `D5/S3/Analytic/ExpRemainderDifferences.g`
- Truth anchor: `D5/S3/Analytic/ExpRemainderDifferences.result`
