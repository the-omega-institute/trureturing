# Polynomial gap for ordered crossing indices

## Abstract

Polynomial gap for ordered crossing indices.

**Theorem 1.1 (The scaled gap is nonnegative under the crossing inequalities).**

$$\forall (a b K L B N k: \mathbb{R}), (0\le a\land a\le b\land 0<k\land k\le B\land B\le N\land N\le L\land (B<L\Rightarrow B+1\le L)\land (k<B\Rightarrow k+1\le B)\land (N<L\Rightarrow N+1\le L)\land a\cdot L\cdot (L-1)/2\le K\land K\le a\cdot N\cdot (N+1)/2+(b-a)\cdot k\cdot (k+1)/2)\Rightarrow 0\le (K-a\cdot L\cdot B/2)\cdot (k\cdot (N-B)-(B-k)\cdot (L-N))+a\cdot L\cdot B\cdot (L-N)\cdot (N-B)/2+L\cdot B\cdot k\cdot (b-a)\cdot (B-k)/2$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/OrderedCrossingGap.gap_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

The ordered lengths are real parameters. The three unit-gap hypotheses recover the discrete inequalities used in Schiavo's Lemma 17 without requiring the parameters to be integer-valued. If sigma is nonnegative, each summand is nonnegative after using the lower bound for K or the equality of the two boundary indices. If sigma is negative, multiply the expression by k+1 and use the upper crossing bound on K. The resulting lower bound is affine in K with nonnegative slope. Its value at the lower endpoint factors into nonnegative terms by the unit gaps.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/OrderedCrossingGap.gap_nonneg`
