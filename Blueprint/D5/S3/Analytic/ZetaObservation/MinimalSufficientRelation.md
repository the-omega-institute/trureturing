# Minimal Sufficient Relation

## Abstract

Equal-size positive zeta samples have a parameter-independent likelihood ratio exactly when their products agree.

**Definition 1.1 (Admissible zeta parameters lie above one).**

$$\operatorname{ZetaParameter}\left(\right) = \operatorname{Subtype}\left(1 < s\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.ZetaParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named parameter type records the normalization threshold.

**Definition 1.2 (The sample product is the multiplicative statistic).**

$$\operatorname{SampleProduct}\left(N\right) = \prod_{n\in N} n$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.sampleProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite natural-number sample is summarized by its product.

**Definition 1.3 (Total log energy sums the logarithms of sample entries).**

$$\operatorname{TotalLogEnergy}\left(N\right) = \sum_{n\in N} \operatorname{Log}\left(n\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.totalLogEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the additive form of the multiplicative statistic.

**Definition 1.4 (The sample likelihood is the product of zeta point masses).**

$$\operatorname{ZetaSampleLikelihood}\left(s, N\right) = \prod_{n\in N} \operatorname{ZetaPointMass}\left(s, n\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zetaSampleLikelihood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint likelihood uses the repository zeta Gibbs PMF.

**Definition 1.5 (The likelihood ratio compares two sample likelihoods).**

$$\operatorname{ZetaLikelihoodRatio}\left(s, N, M\right) = \frac{\operatorname{ZetaSampleLikelihood}\left(s, N\right)}{\operatorname{ZetaSampleLikelihood}\left(s, M\right)}$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zetaLikelihoodRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio remains defined for unequal samples and zero entries.

**Definition 1.6 (Parameter independence means equality at every two parameters).**

$$\operatorname{ParameterIndependent}\left(N, M\right) = \operatorname{ForAllParameters}\left(s, t, \operatorname{ZetaLikelihoodRatio}\left(s, N, M\right) = \operatorname{ZetaLikelihoodRatio}\left(t, N, M\right)\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zetaRatioParameterIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This named relation is the minimal-sufficiency criterion.

**Theorem 1.7 (The joint likelihood separates weight and normalization).**

$$\operatorname{ZetaSampleLikelihood}\left(s, N\right) = \operatorname{Rpow}\left(\operatorname{SampleProduct}\left(N\right), -s\right) \cdot \operatorname{Rpow}\left(\operatorname{InversePartition}\left(s\right), \operatorname{Length}\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zeta_sample_likelihood_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One inverse partition factor appears for every sample entry.

**Theorem 1.8 (Equal sample sizes cancel the partition function).**

$$\operatorname{Length}\left(N\right) = \operatorname{Length}\left(M\right) \Rightarrow \operatorname{ZetaLikelihoodRatio}\left(s, N, M\right) = \operatorname{Rpow}\left(\frac{\operatorname{SampleProduct}\left(M\right)}{\operatorname{SampleProduct}\left(N\right)}, s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zeta_likelihood_ratio_eq_product_ratio_rpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After cancellation only the ratio of sample products remains.

**Theorem 1.9 (The product characterizes parameter-independent ratios).**

$$\left(\left(\operatorname{PositiveSample}\left(N\right) \land \operatorname{PositiveSample}\left(M\right)\right) \land \operatorname{Length}\left(N\right) = \operatorname{Length}\left(M\right)\right) \Rightarrow \left(\operatorname{ParameterIndependent}\left(N, M\right) \Leftrightarrow \operatorname{SampleProduct}\left(N\right) = \operatorname{SampleProduct}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.sample_product_is_minimal_sufficient_relation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive samples of equal length, independence is equivalent to equality of products.

**Theorem 1.10 (Total log energy is the logarithm of the sample product).**

$$\operatorname{PositiveSample}\left(N\right) \Rightarrow \operatorname{TotalLogEnergy}\left(N\right) = \operatorname{Log}\left(\operatorname{SampleProduct}\left(N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.total_log_energy_eq_log_sample_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonzero entries make the logarithmic product identity valid.

**Theorem 1.11 (Product equality is equivalent to log-energy equality).**

$$\left(\operatorname{PositiveSample}\left(N\right) \land \operatorname{PositiveSample}\left(M\right)\right) \Rightarrow \left(\operatorname{SampleProduct}\left(N\right) = \operatorname{SampleProduct}\left(M\right) \Leftrightarrow \operatorname{TotalLogEnergy}\left(N\right) = \operatorname{TotalLogEnergy}\left(M\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.sample_product_eq_iff_total_log_energy_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict monotonicity of the logarithm identifies both statistics.

**Theorem 1.12 (Empty samples have the neutral statistic and constant ratio).**

$$\operatorname{SampleProduct}\left(\operatorname{EmptySample}\left(\right)\right) = 1 \land \left(\operatorname{TotalLogEnergy}\left(\operatorname{EmptySample}\left(\right)\right) = 0 \land \operatorname{ParameterIndependent}\left(\operatorname{EmptySample}\left(\right), \operatorname{EmptySample}\left(\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.empty_samples_parameter_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty product is one and the empty log-energy sum is zero.

**Theorem 1.13 (Singleton independence is equality of the entries).**

$$\left(\operatorname{Positive}\left(n\right) \land \operatorname{Positive}\left(m\right)\right) \Rightarrow \left(\operatorname{ParameterIndependent}\left(\operatorname{Singleton}\left(n\right), \operatorname{Singleton}\left(m\right)\right) \Leftrightarrow n = m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.singleton_parameter_independent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-sample case reduces the product criterion to equality.

**Theorem 1.14 (An entry equal to one changes neither statistic).**

$$\operatorname{SampleProduct}\left(\operatorname{Cons}\left(1, N\right)\right) = \operatorname{SampleProduct}\left(N\right) \land \operatorname{TotalLogEnergy}\left(\operatorname{Cons}\left(1, N\right)\right) = \operatorname{TotalLogEnergy}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.one_entry_is_neutral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication by one and addition of log one are neutral.

**Theorem 1.15 (Permuting a positive sample preserves its likelihood relation).**

$$\left(\operatorname{Permutation}\left(N, M\right) \land \operatorname{PositiveSample}\left(N\right)\right) \Rightarrow \operatorname{ParameterIndependent}\left(N, M\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.perm_samples_parameter_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal multisets have equal products, lengths, and likelihoods.

**Theorem 1.16 (A concrete unequal-product ratio varies with the parameter).**

$$\operatorname{ZetaLikelihoodRatio}\left(2, \operatorname{Singleton}\left(2\right), \operatorname{Singleton}\left(1\right)\right) \ne \operatorname{ZetaLikelihoodRatio}\left(3, \operatorname{Singleton}\left(2\right), \operatorname{Singleton}\left(1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.likelihood_ratio_changes_between_two_and_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Samples two and one give distinct ratios at parameters two and three.

**Theorem 1.17 (Numerator nonzeroness is necessary).**

$$\neg \operatorname{PositiveSample}\left(\operatorname{Singleton}\left(0\right)\right) \land \left(\operatorname{ParameterIndependent}\left(\operatorname{Singleton}\left(0\right), \operatorname{Singleton}\left(1\right)\right) \land \operatorname{SampleProduct}\left(\operatorname{Singleton}\left(0\right)\right) \ne \operatorname{SampleProduct}\left(\operatorname{Singleton}\left(1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.numerator_nonzero_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero numerator makes the ratio constant despite unequal products.

**Theorem 1.18 (Denominator nonzeroness is necessary).**

$$\neg \operatorname{PositiveSample}\left(\operatorname{Singleton}\left(0\right)\right) \land \left(\operatorname{ParameterIndependent}\left(\operatorname{Singleton}\left(1\right), \operatorname{Singleton}\left(0\right)\right) \land \operatorname{SampleProduct}\left(\operatorname{Singleton}\left(1\right)\right) \ne \operatorname{SampleProduct}\left(\operatorname{Singleton}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.denominator_nonzero_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Totalized division at a zero denominator defeats the criterion.

**Theorem 1.19 (Equal sample size is necessary for cancellation).**

$$\operatorname{SampleProduct}\left(\operatorname{Singleton}\left(1\right)\right) = \operatorname{SampleProduct}\left(\operatorname{EmptySample}\left(\right)\right) \land \neg \operatorname{ParameterIndependent}\left(\operatorname{Singleton}\left(1\right), \operatorname{EmptySample}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.equal_sample_size_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The samples one and empty have equal products but differing normalization powers.

**Theorem 1.20 (The inverse-temperature threshold is necessary).**

$$\neg 1 < 1 \land \operatorname{Partition}\left(1\right) = \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.inverse_temperature_bound_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At parameter one the partition function is infinite.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.ZetaParameter`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.denominator_nonzero_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.empty_samples_parameter_independent`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.equal_sample_size_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.inverse_temperature_bound_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.likelihood_ratio_changes_between_two_and_three`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.numerator_nonzero_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.one_entry_is_neutral`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.perm_samples_parameter_independent`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.sampleProduct`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.sample_product_eq_iff_total_log_energy_eq`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.sample_product_is_minimal_sufficient_relation`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.singleton_parameter_independent_iff`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.totalLogEnergy`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.total_log_energy_eq_log_sample_product`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zetaLikelihoodRatio`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zetaRatioParameterIndependent`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zetaSampleLikelihood`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zeta_likelihood_ratio_eq_product_ratio_rpow`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/MinimalSufficientRelation.zeta_sample_likelihood_eq`
