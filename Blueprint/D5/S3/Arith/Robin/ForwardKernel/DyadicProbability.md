# Dyadic logarithmic probability

## Abstract

Normalized logarithmic integration on a positive dyadic interval is a probability measure.

For X>0, let mu_X be Lebesgue measure restricted to (X,2X], with density 1/(x*log(2)). The endpoints have zero Lebesgue measure, so this also represents logarithmic integration over [X,2X].

**Definition 1.1 (Normalized logarithmic measure on a dyadic interval).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real X, the dyadic measure is Lebesgue measure restricted to (X,2X], with density given by the nonnegative part of 1/(x*log(2)). For X>0 this is the logarithmic probability measure dx/(x*log(2)).

**Theorem 1.2 (Conversion to logarithmic integration).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>0 and every real-valued function f, the integral of f against mu_X equals the interval integral of f(x)/x from X to 2X, divided by log(2). The identity uses the total Bochner integral, so it also applies without an integrability premise. Substituting f(x)^2 or abs(f(x))^4 gives the corresponding moment conversions.

**Theorem 1.3 (Conversion of integrability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integrable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>0, interval integrability of f(x)/x on [X,2X] implies integrability of f with respect to mu_X. Multiplication by the constant 1/log(2) and the density criterion for integrability give the result.

**Theorem 1.4 (Unit total mass).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_univ`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_univ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>0, mu_X assigns mass one to the whole real line. The density is continuous and nonnegative on [X,2X], and its integral is log((2X)/X)/log(2)=1.

**Theorem 1.5 (Probability measure).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_isProbabilityMeasure`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_isProbabilityMeasure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive X, the normalized logarithmic measure mu_X is a probability measure, since its total mass is one.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_isProbabilityMeasure`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_univ`
