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

**Theorem 1.6 (Law of the scaled position).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadic_position_map`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadic_position_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>0, the image of mu_X under x maps to x/X is mu_1. The substitution x=Xu cancels X in the logarithmic density, so the position law on [1,2] does not depend on X.

**Theorem 1.7 (Exact logarithmic block mass).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.block_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.block_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 1<=u<=v<=2, the probability of [u,v] under mu_1 is log(v/u)/log(2). Restricting the density to the subinterval reduces the mass to the integral of 1/(x log(2)); its endpoints have zero Lebesgue measure.

**Theorem 1.8 (Endpoint conventions for position blocks).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.position_indicator_Icc_ae_eq_Ioc`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.position_indicator_Icc_ae_eq_Ioc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X>0 and any real endpoints u,v, composing the [u,v] and (u,v] indicators of an arbitrary real function with x/X gives equal functions almost everywhere under mu_X. The position law is mu_1, which assigns zero mass to singletons. Thus a fixed-scale hypothesis stated with closed blocks also applies to disjoint left-open blocks.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.block_mass`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integrable`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_integral`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_isProbabilityMeasure`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadicProbabilityMeasure_univ`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.dyadic_position_map`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/DyadicProbability.position_indicator_Icc_ae_eq_Ioc`
