# Global Log-Log Curvature

## Abstract

The log-log tangent gap is globally trapped by endpoint curvature.

For a,b>1, the tangent gap K(a,b)=log(log(a))+(b-a)/(a log(a))-log(log(b)) is nonnegative and is bounded above and below by the endpoint values of w(t)=(1+log(t))/(t² log(t)²) times (b-a)²/2. The endpoints may coincide or occur in either order.

**Theorem 1.1 (Full-domain quadratic tangent-gap sandwich).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature.loglog_tangent_gap_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature.loglog_tangent_gap_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses ArithmeticMixedCornerResponse.density_antitone for the endpoint density bounds and applies the second-derivative convexity criterion to the two quadratic-corrected gaps. No displacement bound, integer specialization, prime estimate or Robin/RH conclusion is assumed.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LogLogGlobalCurvature.loglog_tangent_gap_quadratic`
- Dependency: [D5/S3/Arith/Robin/ActualRobinClockCovariance](../ActualRobinClockCovariance.md)
- Dependency: [D5/S3/Arith/Robin/ArithmeticMixedCornerResponse](../ArithmeticMixedCornerResponse.md)
