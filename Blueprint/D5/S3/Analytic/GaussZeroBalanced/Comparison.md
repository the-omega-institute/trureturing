# Comparison

## Abstract

Singular endpoint comparison and the Riccati certificate

**Theorem 1.1 (Singular endpoint comparison).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Comparison.singular_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Comparison.singular_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous function that vanishes at the left endpoint and satisfies a strict positive first order differential inequality x u' + P u > 0 on a positive interval is strictly positive in the interval when P is positive. The proof uses the minimum on a compact subinterval and handles both interior and right endpoint minima.

**Theorem 1.2 (Riccati certificate identity).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a function satisfying the zero-balanced Riccati equation, differentiating E = q t f^2 + f - 1 with t = x/(1-x) gives x E' + c(1+2 q t f)E = q t^2 f^2(1-2 q f).

**Theorem 1.3 (Positive Riccati certificate).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, b and 0 < x < 1, the contiguous quotient satisfies (1-f)/(t f^2) < a b/((a+b)(a+b+1)).

**Theorem 1.4 (General contiguous quotient comparison).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Comparison.comparison_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Comparison.comparison_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a and 0 < b1 < b2, the contiguous quotient f(a,b1,x) is strictly larger than f(a,b2,x) throughout (0,1) exactly when b1 b2 <= a(a+1).

**Theorem 1.5 (General Gauss quotient comparison).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Comparison.comparison_iff_quot`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Comparison.comparison_iff_quot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same threshold characterizes strict comparison of the zero-balanced Gauss quotients, using the factor 1-x.

**Theorem 1.6 (Second parameter classification).**

Lean statement: `D5/S3/Analytic/GaussZeroBalanced/Comparison.clause2`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GaussZeroBalanced/Comparison.clause2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0 < a < 1, the two quotients in the second classification are ordered throughout (0,1) exactly when 3/7 <= a.

## References

- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Comparison.certificate_identity`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Comparison.clause2`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Comparison.comparison_iff`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Comparison.comparison_iff_quot`
- Truth anchor: `D5/S3/Analytic/GaussZeroBalanced/Comparison.singular_comparison`
- Dependency: [D5/S3/Analytic/GaussZeroBalanced/Series](Series.md)
