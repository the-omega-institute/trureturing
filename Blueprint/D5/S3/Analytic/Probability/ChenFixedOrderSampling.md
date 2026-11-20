# Fixed-size samples from two balanced strata

## Abstract

Uniform fixed-size sampling and the stratum inclusion identities for Chen's fixed-order problem.

At stage m the sample size is (m+1)^2. Each of the two strata has the cube of the sample size in labels. Values are +1 in the first stratum and -1 in the second. The estimator centers the sample mean at the population mean and multiplies by the square root of the sample size.

**Theorem 1.1 (Positive sample size).**

Lean statement: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sample size is positive at every stage.

**Theorem 1.2 (Population mean).**

Lean statement: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two strata have equal size and opposite values, so the population mean is zero.

**Theorem 1.3 (Erasing order on distinct draws).**

Lean statement: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder_val`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each injective ordered draw, its unordered sample is exactly the finite image of the draw.

**Theorem 1.4 (Uniform law on fixed-size subsets).**

Lean statement: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.map_eraseOrder_cond_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.map_eraseOrder_cond_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Condition the uniform law of ordered draws on having distinct labels, then erase order. Every subset of the required size has the same number of orderings, giving the uniform subset law.

**Theorem 1.5 (Inclusion polynomial).**

Lean statement: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.exists_inclusionPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenFixedOrderSampling.exists_inclusionPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prescribed subset A, there is a polynomial of degree at most the cardinality of A such that, for every real function f, the uniform sample integral of f of the estimator over samples containing A equals its full uniform sample integral weighted by that polynomial of the estimator. On each cell of fixed positive-stratum count, the inclusion fraction is the product of two ratios of binomial coefficients. The two counts are affine in the estimator, giving the degree bound.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.eraseOrder_val`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.exists_inclusionPolynomial`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.map_eraseOrder_cond_uniform`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.populationMean_eq_zero`
- Truth anchor: `D5/S3/Analytic/Probability/ChenFixedOrderSampling.sampleSize_pos`
