# The two real rays

## Abstract

Strict monotonicity and exact ranges of Kummer ratios with shifted upper parameters.

**Theorem 1.1 (Monotonicity and both Gamma endpoints).**

Lean statement: `D5/S3/Analytic/KummerRatio/Result.result`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-sitnik-2010-kummer-ratio-monotonicity` (proved) by `D5/S3/Analytic/KummerRatio/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-sitnik-2010-kummer-ratio-monotonicity","declaration_gid":"D5/S3/Analytic/KummerRatio/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Karp and S. M. Sitnik (2010). *Log-convexity and log-concavity of hypergeometric-like functions*. DOI: [10.1016/j.jmaa.2009.10.057](https://doi.org/10.1016/j.jmaa.2009.10.057). URL: <https://arxiv.org/abs/0902.3073>.

*Commentary.*

For every c>0 and delta>0, if 0<a<b, then R(x)=M(b+delta;c;x) M(a;c;x)/(M(a+delta;c;x) M(b;c;x)) is strictly decreasing for x>0 and its image is exactly (A,1), where A=Gamma(a+delta) Gamma(b)/(Gamma(b+delta) Gamma(a)). If a<b<c-delta, the same ratio is strictly increasing for x<0 and its image is exactly (B,1), where B=Gamma(c-a-delta) Gamma(c-b)/(Gamma(c-b-delta) Gamma(c-a)).

On the positive ray, the logarithmic derivative comparison gives strict decrease. Each Kummer factor is normalized by exp(-x) x^(c-s). The two numerator powers and the two denominator powers have the same total exponent 2c-a-b-delta; the nonzero common factor cancels. The four normalized limits therefore give the Gamma quotient A. Continuity and M(s;c;0)=1 give the endpoint at zero. The intermediate value theorem on the positive ray supplies every value between the two limits, and strict decrease excludes both endpoints.

Kummer reflection cancels the exponential factors in the ratio and gives R(a,b,c,delta,x)=R(c-b-delta,c-a-delta,c,delta,-x). Under a<b<c-delta, the new upper parameters satisfy 0<c-b-delta<c-a-delta. Reflection reverses the order of the argument, so the positive-ray decrease becomes negative-ray increase. It also maps the negative ray onto the positive ray and turns the endpoint A into B.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/Result.result`
- Dependency: [D5/S3/Analytic/KummerRatio/Asymptotics](Asymptotics.md)
- Dependency: [D5/S3/Analytic/KummerRatio/Comparison](Comparison.md)
- Dependency: [D5/S3/Analytic/KummerRatio/Transform](Transform.md)
