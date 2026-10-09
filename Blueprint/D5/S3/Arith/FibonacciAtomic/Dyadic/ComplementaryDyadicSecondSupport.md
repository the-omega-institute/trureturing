# Complementary Dyadic Second Support

## Abstract

A global affine bound and exact high-side recursion for the dyadic cost on Fin(2^a+1).

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

The low-side statement includes its upper endpoint. The global statement below does not classify equality, compute the optimum first coefficient, or assert an effective sampler for every arbitrary real law.

**Theorem 1.2 (Strict high-side scaling).**

$$\forall a: \mathbb{N}, (3 \le a \Rightarrow \forall p: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, (\sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{p}\left(i\right) = 1 \Rightarrow (t0 < \operatorname{min}\left(p\right) \Rightarrow (\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 < \operatorname{q}\left(p, i\right) \land (\sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{q}\left(p, i\right) = 1 \land (\operatorname{L}\left(p\right) = H0 + \frac{\operatorname{L}\left(\operatorname{q}\left(p\right)\right)}{\left(2^{a}\right)^{2}} \land \operatorname{D}\left(p\right) = \frac{\operatorname{D}\left(\operatorname{q}\left(p\right)\right)}{\left(2^{a}\right)^{2}}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.high_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

Put B=2^a, t0=(B-1)/B^2, C=B(a+2)+2B^2, d0=2(B-1), H0=a+2-a/B-2/B^2 and D(p)=L(p)-C min(p)+d0. For a>=3 and a normalized law with min(p)>t0, define q(i)=B^2 p(i)-(B-1). Then q is strictly positive and normalized, L(p)=H0+L(q)/B^2 and D(p)=D(q)/B^2. The minimum also transforms as min(q)=B^2 min(p)-(B-1).

Every p(i) lies between t0 and 1/B. Floors vanish before depth a and equal 2^j-1 at depth a+j, for j<a. These first 2a layers sum to H0. At depth 2a+e, the integer translation formula for floor gives floor(2^(2a+e) p(i))=floor(2^e q(i))+(B-1)2^e, so the residual becomes R(q,e). Splitting the convergent series proves the cost identity; the minimum transformation gives the gap identity. The threshold inequality is strict, so this recursion does not apply to its boundary.

**Theorem 1.3 (Uniform fixed point).**

$$\forall a: \mathbb{N}, (3 \le a \Rightarrow \operatorname{D}\left(u\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.uniform_gap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

The uniform law u(i)=1/(B+1) is strictly high and is fixed by q. Its gap satisfies D(u)=D(u)/B^2. Since B>=8, this forces D(u)=0. Equivalently, L(u)=[B(a+2)+2]/(B+1).

**Theorem 1.4 (Finite positive exit).**

$$\forall a: \mathbb{N}, (3 \le a \Rightarrow \forall p: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, (\sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{p}\left(i\right) = 1 \Rightarrow ((t0 < \operatorname{min}\left(p\right) \land p \neq u) \Rightarrow \exists n: \mathbb{N}, (0 < n \land (\forall k: \mathbb{N}, (k < n \Rightarrow t0 < \operatorname{min}\left(\operatorname{r}\left(p, k\right)\right)) \land (\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 < \operatorname{r}\left(p, n, i\right) \land (\sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{r}\left(p, n, i\right) = 1 \land ((0 < \operatorname{min}\left(\operatorname{r}\left(p, n\right)\right) \land \operatorname{min}\left(\operatorname{r}\left(p, n\right)\right) \le t0) \land \operatorname{D}\left(p\right) = \frac{\operatorname{D}\left(\operatorname{r}\left(p, n\right)\right)}{\left(\left(2^{a}\right)^{2}\right)^{n}}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.finite_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

Let r_k(i)=1/(B+1)+(B^2)^k[p(i)-1/(B+1)]. Then r_0=p, r_(k+1)=q(r_k), and every r_k has total mass one. Its minimum is 1/(B+1)-(B^2)^k[1/(B+1)-min(p)]. For a nonuniform normalized law, min(p)<1/(B+1). Powers of B^2 therefore force a finite first index n>0 with min(r_n)<=t0. All earlier laws are strictly high. Their successive images are positive, so the first exit remains positive and normalized, with 0<min(r_n)<=t0 and D(p)=D(r_n)/(B^2)^n.

**Theorem 1.5 (Global second supporting inequality).**

$$\forall a: \mathbb{N}, (3 \le a \Rightarrow \forall p: \operatorname{Fin}\left((2^{a} + 1)\right) \to \mathbb{R}, ((\forall i: \operatorname{Fin}\left((2^{a} + 1)\right), 0 \le \operatorname{p}\left(i\right) \land \sum_{i \in \operatorname{Fin}\left((2^{a} + 1)\right)}\operatorname{p}\left(i\right) = 1) \Rightarrow (2^{a} (a + 2) + 2 \left(2^{a}\right)^{2}) \operatorname{min}\left(p\right) - 2 (2^{a} - 1) \le \operatorname{L}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.global_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jeremie Lumbroso (2013). *Optimal Discrete Uniform Generation from Coin Flips, and Applications*. URL: <https://arxiv.org/abs/1304.1916v1>.

*Commentary.*

For every a>=3 and every nonnegative normalized real law on B+1 labels, L(p)>=[B(a+2)+2B^2] min(p)-2(B-1). If the minimum is at most t0, apply the low-side theorem. A uniform law has zero gap. Every other strictly high law exits after finitely many rescalings to a positive low-side law; its nonnegative gap transfers back by a positive factor. Thus no low-side hypothesis remains. Zero atoms and dyadic boundaries are included. This inequality alone does not determine the optimal first coefficient or the full cost envelope.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.finite_exit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.global_support`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.high_scaling`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.uniform_gap_zero`
- Dependency: [D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines](../MersenneDyadicSupportLines.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/OptimalLawStrictSlope](../OptimalLawStrictSlope.md)
