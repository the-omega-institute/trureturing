# Palindromic Numerators of OEIS A398690

## Abstract

Every simplified Verlinde row has a palindromic numerator of its expected degree.

For natural r and q, the source function is the real signed sine sum A(r,q)=(2q+1)^(-1) sum from j=0 to 2q of (-1)^(rj) sin((2j+1)pi/(4q+2))^(2-r). The exponent is an integer exponent. The conjectured rows use r=n+3, so r is at least three.

**Definition 1.1 (Simplified Verlinde source sum).**

Lean statement: `D5/S3/Analytic/OeisA398690Palindromic.simplifiedVerlinde`

*Formalization.* `D5/S3/Analytic/OeisA398690Palindromic.simplifiedVerlinde` (`✓ std3`).

*Citation.* F. Chapoton (2026). *OEIS A398690, triangle of polynomials related to Verlinde numbers*. URL: <https://oeis.org/A398690>.

*Commentary.*

This is the A398690 comment's signed finite sum. Its angle 2pi/(8q+4) simplifies to pi/(4q+2). The real power uses the same integer exponent 2-r.

**Theorem 1.2 (All row numerators are palindromic).**

Lean statement: `D5/S3/Analytic/OeisA398690Palindromic.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OeisA398690Palindromic.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a398690-palindromic` (proved) by `D5/S3/Analytic/OeisA398690Palindromic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a398690-palindromic","declaration_gid":"D5/S3/Analytic/OeisA398690Palindromic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* F. Chapoton (2026). *OEIS A398690, triangle of polynomials related to Verlinde numbers*. URL: <https://oeis.org/A398690>.

*Commentary.*

For every natural n there is a real polynomial R of degree exactly n such that its formal power series equals (1-z)^(n+1) times the series whose coefficient at q is A(n+3,q). For every j at most n, the coefficients of R at j and n-j are equal. Chebyshev node moments identify every source coefficient with a polynomial model; the model's reflection gives numerator reciprocity.

## References

- Truth anchor: `D5/S3/Analytic/OeisA398690Palindromic.result`
- Truth anchor: `D5/S3/Analytic/OeisA398690Palindromic.simplifiedVerlinde`
- Dependency: [D5/S3/Analytic/PolynomialReflectionNumerator](PolynomialReflectionNumerator.md)
