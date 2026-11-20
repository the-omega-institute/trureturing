# Integer levels and short digit periods

## Abstract

A bound on the integer levels covered by bounded digits with real weights.

**Theorem 1.1 (A missing short period reduces the integer range).**

$$\forall r k n B M w L, 0 < B \land \operatorname{ShortPeriodsDivide}\left(B, M\right) \land \operatorname{NonintegralTotal}\left(M, w\right) \land \operatorname{DistinctLevels}\left(L, n\right) \land \operatorname{IntegerCoverage}\left(r, k, w, L\right) \Rightarrow n \le (\left\lfloor\frac{k}{B}\right\rfloor+1)\cdot (k+1)^r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/DigitPeriodCapacity.integral_range_le_period_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r, k, n, B and M be natural numbers, with B positive. There are r plus one real weights. A digit can be any integer from zero through k. ShortPeriodsDivide(B,M) means every positive integer below B divides M. NonintegralTotal(M,w) means M times the sum of the weights is nonintegral. Let L be a list of n pairwise distinct integers. IntegerCoverage(r,k,w,L) means every integer in L is represented by a weighted digit vector.

A positive integer is a period for a coordinate if multiplying its weight by that integer produces integer mass. If each coordinate had a period below B, multiplying every weight by M would give an integer. This would make M times the sum an integer. Some coordinate therefore lacks all short periods. Fix the other digits and divide the selected digit by B, rounding down. Two integral representations with the same other digits and quotient must agree, since a positive difference below B would give a short period. Choosing one representation of each level proves the bound.

Each arithmetic premise matters even for one weight. With k equal to two, the weight one half covers zero and one. Taking B equal to zero and M equal to one violates the bound without positivity. Taking B equal to three and M equal to one violates it without the divisibility premise. With B equal to three and M equal to two, the integer weight one covers zero, one and two, showing the need for nonintegrality.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/DigitPeriodCapacity.integral_range_le_period_blocks`
