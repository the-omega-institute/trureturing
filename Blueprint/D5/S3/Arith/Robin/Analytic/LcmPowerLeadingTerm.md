# The scaled threshold limit

## Abstract

The leading asymptotic coefficient of the LCM power threshold at a fixed real parameter.

**Definition 1.1 (The inverse-power coordinate).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.normalizedF`

*Formalization.* `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.normalizedF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With N(t)=(x-t)^kappa-(1-t)^kappa, the normalized expression is log(N(t)/N(x*t))/(kappa*log(x)). For kappa>1 and x>1, at t=0 its value is zero, and its derivative is c(kappa,x).

**Theorem 1.2 (Exact normalization).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x>1 and a positive natural n, the original lcmPowerF from Definition 4.2 equals the normalized expression at t=1/x^n. Factoring x^n from each power base and cancelling its nonzero kappa power proves the identity.

**Theorem 1.3 (Fixed-parameter leading term).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_scaled_limit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_scaled_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real kappa>1 and x>1, F(kappa,x,n)*x^n tends to c(kappa,x)=(x-1)*(x^(kappa-1)-1)/((x^kappa-1)*log(x)) as the natural n tends to infinity.

The normalized function is differentiable at zero with this derivative. Its difference quotient converges along the positive sequence 1/x^n. This proves the fixed-parameter limit. It does not assert a uniform second-order error estimate or limits of parameter derivatives.

The collision argument applies the intermediate value theorem using the leading limits at two fixed parameter endpoints. It therefore does not require the uniform remainder estimate of Lemma 3.1.

**Theorem 1.4 (Continuity in the parameter).**

Lean statement: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.continuousOn_lcmPowerF`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.continuousOn_lcmPowerF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At x>1 and a positive natural exponent, the numerator and denominator power differences are positive for kappa>1. Their quotient, logarithm, and division by kappa*log(x) are continuous throughout that interval.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.continuousOn_lcmPowerF`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_normalized`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.lcmPowerF_scaled_limit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLeadingTerm.normalizedF`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerCollisionCoefficient](LcmPowerCollisionCoefficient.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen](LcmPowerLemmaFifteen.md)
