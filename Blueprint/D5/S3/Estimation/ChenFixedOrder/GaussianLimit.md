# Gaussian limit for balanced finite populations

## Abstract

A Gaussian limit for the balanced-sign estimator under uniform fixed-size sampling.

**Definition 1.1 (Standard Gaussian probability law).**

$$\operatorname{standardGaussian} : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), (\operatorname{standardGaussian} : \operatorname{Measure}\left(\mathbb{R}\right)) = \operatorname{gaussianReal}\left(0, 1\right)$$

*Formalization.* `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.standardGaussian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the Gaussian limit of the balanced-sign estimator.

**Theorem 1.2 (Estimator law on uniform subsets).**

$$\operatorname{Tendsto}\left(m \mapsto \operatorname{ProbabilityMeasure.map}\left(\operatorname{uniformSampleMeasure}\left(m\right), \operatorname{estimator}\left(m\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{standardGaussian}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.uniformSampleLaw_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With replacement, the uniform label law gives each sign probability 1/2. The centered estimator is the normalized partial sum in the independent central limit theorem along the square sample sizes.

The union bound over distinct position pairs bounds the probability of a repeated label by the square of the sample size divided by the population size. This tends to zero, and conditioning on distinct labels changes each bounded test expectation by at most twice its bound times the collision probability.

Erasing order takes the conditioned draw law to the uniform law on fixed-size subsets and preserves the estimator on distinct draws. Thus the Gaussian limit passes to the uniform subset law.

## References

- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.standardGaussian`
- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.uniformSampleLaw_tendsto`
- Dependency: [D5/S3/Analytic/Probability/ChenFixedOrderSampling](../../Analytic/Probability/ChenFixedOrderSampling.md)
