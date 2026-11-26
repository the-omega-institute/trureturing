# Weighted cyclotomic correction

## Abstract

The prime-power weighted carry identity and its explicit linear sampled correction.

**Definition 1.1 (Prime-power readout).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.primePowerReadout`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.primePowerReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prime power p^t at most X with t positive, multiply the coefficient at p^t by its weight and by log p, then add the contributions.

**Definition 1.2 (Weighted Chebyshev sum).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedPsi`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedPsi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set every coefficient in the prime-power readout to one.

**Theorem 1.3 (Weighted von Mangoldt sum).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedPsi_eq_sum_vonMangoldt`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedPsi_eq_sum_vonMangoldt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real-valued weight on the natural numbers and every natural cutoff x, the readout equals the sum of w(n) times the von Mangoldt function at n for 1 ≤ n ≤ x.

Each prime power has a unique prime base and positive exponent. This bijection identifies the summands, and the von Mangoldt function vanishes off prime powers.

**Definition 1.4 (Weighted carries).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedB`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At cutoff 4N+1, the coefficient of a conductor is the sum of the row carries and the sum of the carries restricted by the index-dependent gcd cutoffs.

**Definition 1.5 (Weighted factorial correction).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedK`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedK` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At cutoff 4N+1, assign coefficient N to conductor two, the floor of N/r to each odd conductor r, and zero to higher powers of two.

**Definition 1.6 (Weighted residue indicator).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedIndicator`

*Formalization.* `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read the residue indicator at each prime power through cutoff 4N+1.

**Theorem 1.7 (Exact weighted carry identity).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedB_add_weightedK_add_weightedIndicator`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedB_add_weightedK_add_weightedIndicator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real weights and every natural N, the weighted carries, factorial correction and residue indicator add up to the sum of weighted Chebyshev values at 4i+1 for 0 ≤ i ≤ N.

The prime-power deficit equals the factorial coefficient plus the residue indicator. Padding the sampled sums to the common cutoff 4N+1 gives the same coefficient at each prime power.

**Theorem 1.8 (Explicit weighted sample error).**

Lean statement: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.corrected_weighted_sample_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.corrected_weighted_sample_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and every nonnegative bound W with 0 ≤ w(r) ≤ W for all r, the absolute difference between the weighted carries plus factorial correction and the sum of weighted Chebyshev values at 4i for 0 ≤ i ≤ N is at most W times (4N+1) times (log 4 + 4).

The residue indicator contributes between zero and W times (4N+1) log 4. The change from 4i to 4i+1 also contributes a nonnegative amount. Each prime power can occur at only one of these boundaries, so the Chebyshev bound controls their total contribution.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.corrected_weighted_sample_error`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.primePowerReadout`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedB`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedB_add_weightedK_add_weightedIndicator`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedIndicator`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedK`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedPsi`
- Truth anchor: `D5/S3/Arith/FactorialRatio/ElementaryCyclotomicWeightedCorrection.weightedPsi_eq_sum_vonMangoldt`
- Dependency: [D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection](ElementaryCyclotomicCorrection.md)
- Dependency: [D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd](ElementaryCyclotomicGcd.md)
