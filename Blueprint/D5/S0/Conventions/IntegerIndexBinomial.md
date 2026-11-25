# The binomial coefficient with an integer lower index

## Abstract

A binomial coefficient whose lower index is an integer is read as zero when that index is negative and as the ordinary binomial coefficient otherwise.

**Definition 1.1 (The binomial coefficient C(m, j) for an integer j).**

$$\operatorname{binom}\left(m, j\right) = \operatorname{if} j < 0 \operatorname{then} 0 \operatorname{else} \operatorname{choose}\left(m, \operatorname{toNat}\left(j\right)\right)$$

*Formalization.* `D5/S0/Conventions/IntegerIndexBinomial.binom` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number m and an integer j, binom(m, j) uses C(m, j) on the nonnegative constructor and zero on the negative constructor. The strict binomial coefficient satisfies Pascal's recurrence, including the cases j = 0 and j > m. The executable standard interface supports existing sums over integer ranges.

**Definition 1.2 (The integer ballot coefficient).**

$$\forall r: \mathbb{N}, \forall b: \mathbb{N}, \operatorname{ballotE}\left(r, b\right) = \operatorname{binom}\left(r + b - 1, (b: \mathbb{Z}) - 1\right) - \operatorname{binom}\left(r + b - 1, (b: \mathbb{Z}) - 2\right)$$

*Formalization.* `D5/S0/Conventions/IntegerIndexBinomial.ballotE` (`✓ std3`).

*Citation.* Umesh Shankar (2026). *Avoiding patterns with three distinct letters in Canon permutations*. DOI: [10.48550/arXiv.2608.30002](https://doi.org/10.48550/arXiv.2608.30002).

*Commentary.*

The upper binomial index uses natural subtraction; the lower indices use integer subtraction. IntegerIndexBinomial.binom is zero at a negative lower index. Thus ballotE(r,1)=1, including r=0. The Shankar closed form uses ballotE(r,b), and the degree-j coefficient of the terminating Luschny array uses ballotE(k,j+1).

## References

- Truth anchor: `D5/S0/Conventions/IntegerIndexBinomial.ballotE`
- Truth anchor: `D5/S0/Conventions/IntegerIndexBinomial.binom`
- Dependency: [D5/S0/Conventions/IntegerIndexBinomial/Native](IntegerIndexBinomial/Native.md)
