# The binomial coefficient with an integer lower index

## Abstract

A binomial coefficient whose lower index is an integer is read as zero when that index is negative and as the ordinary binomial coefficient otherwise.

**Definition 1.1 (The binomial coefficient C(m, j) for an integer j).**

$$\operatorname{binom}\left(m, j\right) = \operatorname{if} j < 0 \operatorname{then} 0 \operatorname{else} \operatorname{choose}\left(m, \operatorname{toNat}\left(j\right)\right)$$

*Formalization.* `D5/S0/Conventions/IntegerIndexBinomial.binom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number m and an integer j, binom(m, j) is zero when j is negative and the binomial coefficient C(m, j) otherwise, so it also vanishes when j exceeds m. Sums of binomial coefficients over integer ranges use it to drop the terms with a negative lower index.

## References

- Truth anchor: `D5/S0/Conventions/IntegerIndexBinomial.binom`
