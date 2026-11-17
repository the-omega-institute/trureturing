# Macroscopic dyadic moments

## Abstract

Positive powers of a common logarithmically sampled dyadic scale have strictly positive covariance.

Let U have density 1/(u log 2) on [1,2], and define M(gamma) as the integral of u^gamma against this probability measure. This integral definition also includes gamma=0, where M(0)=1.

**Definition 1.1 (Moment of the logarithmic dyadic scale).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadicMacroMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadicMacroMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real exponent gamma, dyadicMacroMoment(gamma) is the integral of u^gamma against du/(u*log(2)) on [1,2]. In particular, its value at gamma=0 is one.

**Theorem 1.2 (Evaluation of positive power moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For gamma>0, M(gamma)=(2^gamma-1)/(gamma log 2). Normalize the logarithmic integral and integrate u^(gamma-1) between 1 and 2.

**Theorem 1.3 (Positivity of power moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For gamma>0, M(gamma)>0: the numerator 2^gamma-1 and the denominator gamma log 2 are both strictly positive.

**Theorem 1.4 (Strict covariance of two powers).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_strict_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_strict_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a>0 and b>0, M(a)M(b)<M(a+b). Thus two positive powers of the same scale have strictly positive covariance.

Write I(t) for the integral of u^t/u over [1,2] and J(u) for the integral of (u^a-v^a)(u^b-v^b)/v over [1,2]. Both powers are strictly increasing, so the inner integrand is nonnegative. At u=2 and v=1 it is strictly positive. Continuity gives J(2)>0, then strict positivity of the integral of J(u)/u. Expansion evaluates this last integral as 2(log 2 I(a+b)-I(a)I(b)). Dividing by (log 2)^2 proves the strict moment inequality. The common scale, rather than any additional coupling assumption, supplies this positive covariance.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadicMacroMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_eq`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_pos`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicMacroMoments.dyadic_macro_moment_strict_mul`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/DyadicProbability](DyadicProbability.md)
