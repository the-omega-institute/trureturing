# Aggregate Prime Exponents

## Abstract

Aggregate prime exponents reconstruct nonzero samples and specialize to the one-sample geometric law.

**Definition 1.1 (The aggregate exponent sums sample factorizations).**

$$\operatorname{AggregateExponent}\left(p\right) = \sum_{j\in \operatorname{Fin}\left(m\right)} \operatorname{V}\left(p, \operatorname{At}\left(N, j\right)\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregateExponent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural base, the named statistic sums its factorization exponents across the finite sample.

**Theorem 1.2 (Aggregate exponents reconstruct a nonzero sample product).**

$$\prod_{j} \operatorname{At}\left(N, j\right) = \prod_{p} p^{{\operatorname{AggregateExponent}\left(p\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.sample_product_eq_prime_power_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof reuses natural-number unique factorization. Nonzeroness is required because Mathlib totalizes the factorization of zero.

**Theorem 1.3 (A zero singleton is a reconstruction counterexample).**

$$\neg \prod_{j} 0 = \prod_{p} p^{{\operatorname{AggregateExponent}\left(p\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.sample_nonzero_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the singleton sample containing zero, the sample product is zero while the product represented by its aggregate factorization is one.

**Theorem 1.4 (The empty sample has zero aggregate and product one).**

$$\operatorname{Aggregate}\left(\operatorname{EmptySample}\left(\right)\right) = 0 \land \operatorname{Product}\left(\operatorname{EmptySample}\left(\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This records both degenerate identities without any probabilistic or nonzeroness assumption.

**Theorem 1.5 (A singleton aggregate is its sole factorization).**

$$\operatorname{Aggregate}\left(\operatorname{Singleton}\left(n\right)\right) = \operatorname{Factorization}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing over the one-element sample index leaves exactly the original factorization.

**Theorem 1.6 (Adjoining one leaves the aggregate unchanged).**

$$\operatorname{Aggregate}\left(\operatorname{Cons}\left(1, N\right)\right) = \operatorname{Aggregate}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_one_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorization of one is zero at every coordinate, so a sample value one contributes no exponent.

**Theorem 1.7 (The one-sample aggregate law is geometric).**

$$\operatorname{Probability}\left(\operatorname{AggregateExponent}\left(p\right) = c\right) = {1 - p^{{-s}}} \cdot p^{{-c \cdot s}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For exponent above one and a prime coordinate, the imported zeta factorization law gives the exact mass at every natural count.

**Theorem 1.8 (The one-sample zero mass is one minus the prime weight).**

$$\operatorname{Probability}\left(\operatorname{AggregateExponent}\left(p\right) = 0\right) = 1 - p^{{-s}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton_zero_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Setting the count to zero in the geometric law removes the power-law occupation factor.

**Theorem 1.9 (One-sample aggregate prime coordinates are mutually independent).**

$$\operatorname{MutuallyIndependent}\left(p\mapsto \operatorname{AggregateExponent}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton_iIndep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The family statement is exactly the repository's prime-factorization independence theorem after simplifying a singleton sum.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregateExponent`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_empty`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_one_cons`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton_iIndep`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton_law`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.aggregate_exponent_singleton_zero_mass`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.sample_nonzero_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/AggregatePrimeExponent.sample_product_eq_prime_power_product`
