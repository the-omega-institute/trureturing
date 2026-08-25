# The Distinct Prime Factor Count Bound

## Abstract

A nonzero integer has at most its floor base-two logarithm many distinct prime factors.

**Theorem 1.1 (Distinct prime factors obey a floor logarithmic bound).**

$$2^{{\operatorname{omega}\left(\left|d\right|\right)}} \le \operatorname{distinctPrimeProduct}\left(\left|d\right|\right) \land \left(\operatorname{distinctPrimeProduct}\left(\left|d\right|\right) \le \left|d\right| \land \operatorname{omega}\left(\left|d\right|\right) \le \operatorname{floorLog2}\left(\left|d\right|\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeProducts/DistinctPrimeFactorCountBound.distinct_prime_factor_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be nonzero. Every prime divisor of its absolute value is at least two, so their product is at least two raised to the number of distinct prime divisors.

The product of the distinct prime divisors is the natural-number radical of the absolute value. The radical divides a nonzero natural number and is therefore at most that number.

Combining the two inequalities and applying the defining adjunction for the natural floor logarithm gives the stated base-two bound.

## References

- Truth anchor: `D5/S3/Analytic/PrimeProducts/DistinctPrimeFactorCountBound.distinct_prime_factor_count_bound`
