# Logarithmic derivatives and finite parameter increments

## Abstract

Comparison of positive solutions of the confluent hypergeometric equation.

**Definition 1.1 (Positive regular solution families).**

Lean statement: `D5/S3/Analytic/KummerRatio/Comparison.SolutionFamily`

*Formalization.* `D5/S3/Analytic/KummerRatio/Comparison.SolutionFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A solution family consists of y, its first derivative and its second derivative. For every positive parameter s, the function y(s,x) is positive on the closed positive ray, y and its first derivative are continuous there, the two derivative identities hold on the positive ray, and x y''+(c-x)y'-s y=0.

**Theorem 1.2 (Strict decrease for a positive solution family).**

Lean statement: `D5/S3/Analytic/KummerRatio/Comparison.solution_ratio_strictAntiOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Comparison.solution_ratio_strictAntiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c be positive. For every positive parameter s, let y(s,x) be positive for x at least zero, with y and its first derivative continuous there, twice differentiable at every positive x, and satisfying x y''+(c-x)y'-s y=0. For positive delta and 0<a<b, the quotient y(b+delta,x)y(a,x)/(y(a+delta,x)y(b,x)) strictly decreases on the positive ray. The normalization at zero is arbitrary.

Put h(s,x)=y'(s,x)/y(s,x). The Riccati equation and the weight x^c exp(-x)y(u,x)y(v,x) show that h(v,x)>h(u,x) whenever 0<u<v and x>0. The weight vanishes continuously at zero. A second weighted identity shows that h(b+delta,x)-h(b,x) is strictly less than h(a+delta,x)-h(a,x). The difference of these two finite increments is the logarithmic derivative of the positive quotient.

**Theorem 1.3 (Strict decrease of the Kummer ratio).**

Lean statement: `D5/S3/Analytic/KummerRatio/Comparison.ratio_strictAntiOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Comparison.ratio_strictAntiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>0, delta>0 and 0<a<b, the quotient M(b+delta;c;x)M(a;c;x)/(M(a+delta;c;x)M(b;c;x)) strictly decreases for x>0. The entire defining series supplies the differential equation and the continuous derivatives. Nonnegative coefficients give M(s;c;x) at least one for positive s and nonnegative x, so the general positive solution comparison applies.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/Comparison.SolutionFamily`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Comparison.ratio_strictAntiOn`
- Truth anchor: `D5/S3/Analytic/KummerRatio/Comparison.solution_ratio_strictAntiOn`
- Dependency: [D5/S3/Analytic/KummerRatio/Series](Series.md)
