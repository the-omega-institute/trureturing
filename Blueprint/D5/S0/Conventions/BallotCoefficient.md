# Ballot coefficients

## Abstract

Ballot coefficients are differences of adjacent binomial coefficients.

**Definition 1.1 (The integer ballot coefficient).**

$$\forall r: \mathbb{N}, \forall b: \mathbb{N}, \operatorname{ballotE}\left(r, b\right) = \operatorname{binom}\left(r + b - 1, (b: \mathbb{Z}) - 1\right) - \operatorname{binom}\left(r + b - 1, (b: \mathbb{Z}) - 2\right)$$

*Formalization.* `D5/S0/Conventions/BallotCoefficient.ballotE` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper binomial index uses natural subtraction; the lower indices use integer subtraction. IntegerIndexBinomial.binom is zero at a negative lower index. Thus ballotE(r,1)=1, including r=0. The Shankar closed form uses ballotE(r,b), and the degree-j coefficient of the terminating Luschny array uses ballotE(k,j+1).

## References

- Truth anchor: `D5/S0/Conventions/BallotCoefficient.ballotE`
- Dependency: [D5/S0/Conventions/IntegerIndexBinomial](IntegerIndexBinomial.md)
