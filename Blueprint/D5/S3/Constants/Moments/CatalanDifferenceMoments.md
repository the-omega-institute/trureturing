# Catalan Difference Moment Ratios

## Abstract

Unit forward differences of Catalan moments are positive and obey a uniform ratio envelope.

**Theorem 1.1 (A uniform envelope for every difference order).**

Lean statement: `D5/S3/Constants/Moments/CatalanDifferenceMoments.catalan_difference_ratio_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CatalanDifferenceMoments.catalan_difference_ratio_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write M(m) for the original catalanMoment, the m-th moment of four times a beta variable with parameters one half and three halves. Its exact moment formula is M(m)=Catalan(m). For natural L and k let A(L,k) denote the k-fold unit forward difference of M at L. For every L at least one and every k, A(L,k) is strictly positive, 3(L+k)A(L,k) is at most (L+k+2)A(L,k+1), and A(L,k+1) is strictly less than 3A(L,k).

The Catalan recurrence gives (L+2)A(L,1)=3L A(L,0). The shift identity A(L+1,k)=A(L,k)+A(L,k+1) transports this equation to (L+s+3)A(L,s+2)=(3L+2s+2)A(L,s+1)+3(s+1)A(L,s) for every natural s. Simultaneous induction preserves positivity and the two ratio inequalities. For the upper inequality, the coefficient difference (k+7)(L+k)-(k+1)(L+k+2)=6L+4k-2 is positive. This includes L=1, order zero, and both parities.

For n at least 34, 1 <= d <= floor(n/2)-4 and 0 <= r < d, define omega(n,d,r) as the sum from j=0 through d-r+2 of (-1)^j choose(d-r+2,j) Catalan(n-r-j-4). The binomial expansion of the forward difference, with the summation index reflected, identifies this sum with A(L,k) for L=n-d-6 and k=d-r+2. Every index satisfies j <= k, so natural subtraction agrees with the indicated integer indices. These parameters obey L >= 15, k >= 3 and L+k=n-r-4 >= 18. Incrementing r reduces k by one; the endpoint r=d-1 therefore compares orders three and two.

Put s=L+k. The lower envelope at k-1 and positivity imply A(L,k-1)/A(L,k) <= (s+1)/(3(s-1)). For s >= 18 this is at most 19/51, which is strictly less than 28561/76415: the cross-product margin 51*28561-19*76415 is 4726. Thus omega(n,d,r+1) <= (28561/76415) omega(n,d,r) throughout the stated domain. This is a bound for the numerical count sequence. Identifying an actual polygon completion fiber and deriving a bound for a common intersecting family require their own combinatorial hypotheses.

## References

- Truth anchor: `D5/S3/Constants/Moments/CatalanDifferenceMoments.catalan_difference_ratio_envelope`
- Dependency: [D5/S3/Constants/Moments/CatalanSquareHankelGrowth](CatalanSquareHankelGrowth.md)
