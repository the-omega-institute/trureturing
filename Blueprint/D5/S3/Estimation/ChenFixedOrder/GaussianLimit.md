# Gaussian limit for balanced finite populations

## Abstract

A Gaussian limit for the balanced-sign estimator under uniform fixed-size sampling.

At stage m the sample size n is (m+1)^2. The two strata each contain n^3 labels, with values +1 and -1 respectively. The population mean is zero. For both ordered draws and subsets of size n, the estimator is the sample mean minus the population mean, multiplied by the square root of n.

**Theorem 1.1 (Independent draws).**

Lean statement: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.withReplacement_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.withReplacement_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform label law gives each sign probability 1/2. Its independent product, mapped coordinatewise to signs, agrees with the corresponding finite restriction of the infinite Bernoulli product. The centered estimator is the normalized partial sum in the i.i.d. central limit theorem, along the subsequence of square sample sizes.

**Theorem 1.2 (Collision probability).**

Lean statement: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.collisionMass_le`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.collisionMass_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each pair of distinct draw positions has equal labels with probability at most the inverse population size. The union bound over the ordered position pairs gives at most n^2/(2n^3), which tends to zero. The event of distinct labels has positive probability at every stage.

**Theorem 1.3 (Effect of conditioning).**

Lean statement: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.distinctLaw_test_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.distinctLaw_test_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable real test bounded in absolute value by C, the difference between its conditional and unconditional estimator expectations has absolute value at most twice C times the collision probability. This follows by splitting the unconditional integral over the distinct event and its complement.

**Theorem 1.4 (Conditioned estimator law).**

Lean statement: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.distinctLaw_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.distinctLaw_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each bounded continuous test, the difference from its with-replacement expectation tends to zero. The estimator law given distinct labels therefore converges weakly to the standard Gaussian.

**Theorem 1.5 (Estimator law on uniform subsets).**

Lean statement: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.uniformSampleLaw_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.uniformSampleLaw_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite sampling transport theorem maps the conditioned draw law to the uniform law on subsets of size n by erasing positions. This preserves the sum of the values when the labels are distinct. The resulting estimator law, whose underlying measure is the baseline of the density bridge, converges weakly to the standard Gaussian.

## References

- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.collisionMass_le`
- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.distinctLaw_tendsto`
- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.distinctLaw_test_bound`
- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.uniformSampleLaw_tendsto`
- Truth anchor: `D5/S3/Estimation/ChenFixedOrder/GaussianLimit.withReplacement_tendsto`
- Dependency: [D5/S3/Analytic/Probability/ChenFixedOrderSampling](../../Analytic/Probability/ChenFixedOrderSampling.md)
