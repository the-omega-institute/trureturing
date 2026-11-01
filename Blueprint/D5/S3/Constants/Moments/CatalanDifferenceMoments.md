# Catalan Difference Moment Ratios

## Abstract

Unit forward differences of Catalan moments are positive and obey a uniform ratio envelope.

**Theorem 1.1 (A uniform envelope for every difference order).**

$$\forall (L: \mathbb{N}), (\forall (k: \mathbb{N}), ((1 \le L) \Rightarrow (0 < \operatorname{A}(L,k) \land \left((3\cdot(L+k)\cdot\operatorname{A}(L,k) \le (L+k+2)\cdot\operatorname{A}(L,k+1)) \land (\operatorname{A}(L,k+1) < 3\cdot\operatorname{A}(L,k))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/CatalanDifferenceMoments.catalan_difference_ratio_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write M(m) for the original catalanMoment, the m-th moment of four times a beta variable with parameters one half and three halves. Its exact moment formula is M(m)=Catalan(m). For natural L and k let A(L,k) denote the k-fold unit forward difference of M at L. For every L at least one and every k, A(L,k) is strictly positive, 3(L+k)A(L,k) is at most (L+k+2)A(L,k+1), and A(L,k+1) is strictly less than 3A(L,k).

The Catalan recurrence gives (L+2)A(L,1)=3L A(L,0). The shift identity A(L+1,k)=A(L,k)+A(L,k+1) transports this equation to (L+s+3)A(L,s+2)=(3L+2s+2)A(L,s+1)+3(s+1)A(L,s) for every natural s. Simultaneous induction preserves positivity and the two ratio inequalities. For the upper inequality, the coefficient difference (k+7)(L+k)-(k+1)(L+k+2)=6L+4k-2 is positive. This includes L=1, order zero, and both parities.

For every natural n at least 15, put m=floor(n/2)-4, c_r=Catalan(n-r-2), V_r=c_(r+2)-2c_(r+3)+c_(r+4), and G_d=sum_(r=0)^d (-1)^r choose(d,r) V_r-V_d. These are numerical definitions. For every 1 <= d <= m, the original moment formula gives V_r=A(n-r-6,2) for 0 <= r <= d. Reflecting the binomial forward-difference expansion of the function x -> A(x,2), and composing its d and two difference orders, gives G_d=A(L,d+2)-A(L,2), where L=n-d-6 >= 6. The summation bound r <= d and d+4 <= floor(n/2) justify every natural subtraction; no parity or additional lower cutoff on n is required.

At L >= 6 the positive lower envelope makes A(L,k+1)>A(L,k) for every natural k: the coefficient excess is 2(L+k)-2>0. Strict monotonicity in the order therefore gives G_d>0 for 1 <= d <= m. If 1 <= d < m, set L'=n-d-7 >= 6. The shift identity gives G_d-G_(d+1)=A(L',d+2)-A(L',3) >= 0. Finally direct expansion gives G_1=G_2=V_0-2V_1=c_2-4c_3+5c_4-2c_5=h_n. This establishes the full numerical positivity, monotonicity and endpoint equalities. It does not identify any number with an actual trace fiber, establish a partition or total-cardinality identity, or construct compatible ears.

For n at least 34, 1 <= d <= floor(n/2)-4 and 0 <= r < d, define omega(n,d,r) as the sum from j=0 through d-r+2 of (-1)^j choose(d-r+2,j) Catalan(n-r-j-4). The binomial expansion of the forward difference, with the summation index reflected, identifies this sum with A(L,k) for L=n-d-6 and k=d-r+2. Every index satisfies j <= k, so natural subtraction agrees with the indicated integer indices. These parameters obey L >= 15, k >= 3 and L+k=n-r-4 >= 18. Incrementing r reduces k by one; the endpoint r=d-1 therefore compares orders three and two.

Put s=L+k. The lower envelope at k-1 and positivity imply A(L,k-1)/A(L,k) <= (s+1)/(3(s-1)). For s >= 18 this is at most 19/51, which is strictly less than 28561/76415: the cross-product margin 51*28561-19*76415 is 4726. Thus omega(n,d,r+1) <= (28561/76415) omega(n,d,r) throughout the stated domain. This is a bound for the numerical count sequence. Identifying an actual polygon completion fiber and deriving a bound for a common intersecting family require their own combinatorial hypotheses.

## References

- Truth anchor: `D5/S3/Constants/Moments/CatalanDifferenceMoments.catalan_difference_ratio_envelope`
- Dependency: [D5/S3/Constants/Moments/CatalanSquareHankelGrowth](CatalanSquareHankelGrowth.md)
