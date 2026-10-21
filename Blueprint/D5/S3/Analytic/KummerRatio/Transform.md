# Kummer reflection

## Abstract

Reflection of the real argument and complementary upper parameter in the Kummer series.

**Theorem 1.1 (Complementary upper parameters).**

Lean statement: `D5/S3/Analytic/KummerRatio/Transform.kummer_transform`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/Transform.kummer_transform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s, positive c and real x, M(s;c;x)=exp(x) M(c-s;c;-x). There is no positivity restriction on the upper parameter s or on the reflected upper parameter c-s.

The finite binomial sum of (-1)^k times choose(n,k) times (t)_k/(c)_k equals (c-t)_n/(c)_n. Splitting the binomial coefficients at rank n+1 proves this identity by induction, with a simultaneous shift of t and c. Applying it at t=c-s identifies each coefficient in the product of the exponential series and M(c-s;c;-x). Both series converge absolutely for every real x, so their Cauchy product gives the function identity.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/Transform.kummer_transform`
- Dependency: [D5/S3/Analytic/KummerRatio/Series](Series.md)
