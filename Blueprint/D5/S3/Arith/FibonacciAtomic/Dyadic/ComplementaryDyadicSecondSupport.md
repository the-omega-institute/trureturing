# Complementary Dyadic Second Support

## Abstract

A uniform low-side affine bound for the dyadic cost on Fin(2^a+1).

**Theorem 1.1 (Low-side supporting inequality).**

$$\forall a: \mathbb{N}, (3 \le a \Rightarrow \forall p: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, (((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 \le \operatorname{p}\left(i\right)) \land \sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{p}\left(i\right) = 1) \Rightarrow \forall t: \mathbb{R}, (t = \operatorname{min}\left(p\right) \Rightarrow (t \le \frac{(2^{a} - 1)}{\left(2^{a}\right)^{2}} \Rightarrow (2^{a} (a + 2) + 2 \left(2^{a}\right)^{2}) t - 2 (2^{a} - 1) \le \operatorname{L}\left(p\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

Let a>=3, B=2^a and m=B+1. For every nonnegative real law p on Fin(m) whose coordinates sum to one, put t=min_i p(i). If t<=(B-1)/B^2, then L(p)>=[B(a+2)+2B^2]t-2(B-1). Here R(p,d) and L(p) are the residual and cost of Dyadic Cost Support Lines: R(p,d)=2^d-sum_i floor(2^d p(i)), and L(p)=sum_d R(p,d)/2^d. The nonnegative tail series converges on the real probability simplex. Zero coordinates and terminating dyadic expansions are included.

The classical Knuth-Yao DDG expression, recalled by Lumbroso in Section 2.1 and used in Saad, Freer, Rinard and Mansinghka's Fast Loaded Dice Roller (arXiv:2003.03830), supplies the cost model. Those sources do not supply this affine inequality on the complementary simplex. The Mersenne support inequalities supply the comparison used in the lowest interval.

Write f_d(x)=x-floor(2^d x)/2^d. Each f_d is nonnegative, and normalization gives sum_i f_d(p(i))=R(p,d)/2^d. Thus every finite collection of complete depth layers gives a lower bound for L. When t<=(B-3)/B^2, two merges reduce the law to B-1 labels. A merge preserves normalization and the common lower bound t, and floor superadditivity decreases every residual. The Mersenne second support line then dominates the required bound.

For (B-3)/B^2<t<=(B-2)/B^2, every atom is below 3/B. All floors before depth a-1 vanish. At depth a-1, every floor is at most one, and at most one atom can be at least 2/B: two such atoms and the remaining B-1 atoms would have total mass above one. The first a layers therefore contribute at least a-2/B, which dominates the affine bound throughout this interval.

For (B-2)/B^2<t<=(B-1)/B^2, put delta=1-Bt and S={i:Bp(i)<1}, with N=|S|. Then 1<=B delta<2. Normalization gives sum_i(1-Bp(i))=1, while positive deficits occur only in S and each is at most delta, so N delta>=1. The first a layers contribute exactly a. For i in S and 0<=j<a, the next floors equal 2^j-1; these a layers contribute at least k/B per atom, where k=2-2/B-a delta>=0. Their total is at least Nk/B.

The factorization k-B delta[4-(2B+a+2)delta]=(B delta-1)[(2B+a+2)B delta-2(B-1)]/B>=0, together with N delta>=1, gives Nk/B>=4-(2B+a+2)delta. Adding the first a layers yields exactly [B(a+2)+2B^2]t-2(B-1). The upper endpoint is included in this argument.

This theorem concerns the low interval only. It does not establish the same inequality above (B-1)/B^2, classify equality, compute the optimum first coefficient, or assert an effective sampler for every arbitrary real law.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines](../MersenneDyadicSupportLines.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope](../OptimalLawStrictSlope.md)
