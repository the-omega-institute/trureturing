# Strong Divisibility and the Prefix Lcm

## Abstract

A positive strong divisibility sequence has an exact prefix-lcm logarithm as a Mertens dilation at every natural cutoff.

**Theorem 1.1 (Exact logarithmic Mertens dilation).**

$$\forall u: \mathbb{N} \to \mathbb{N}, ((\forall n\in \mathbb{N}, 0< n\Rightarrow 0< \operatorname{u}\left(n\right))\land (\forall a,b\in \mathbb{N}, 0< a\land 0< b\Rightarrow \operatorname{gcd}\left(\operatorname{u}\left(a\right), \operatorname{u}\left(b\right)\right)= \operatorname{u}\left(\operatorname{gcd}\left(a, b\right)\right)))\Rightarrow \forall N\in \mathbb{N}, \operatorname{log}\left(\operatorname{L}\left(N\right)\right)= \sum_{0< d\le N}\operatorname{log}\left(\operatorname{u}\left(d\right)\right)\sum_{0< m\le \lfloor\frac{N}{d}\rfloor}\operatorname{mu}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/StrongDivisibilityLcmMertens.log_prefix_lcm_eq_mertens_dilation` (`✓ std3`). ∎

*Citation.* Andrzej Nowicki (2013). *Strong divisibility and lcm-sequences*. URL: <https://arxiv.org/abs/1310.2416v1>.

*Commentary.*

Let u map natural numbers to natural numbers. Assume u(n)>0 for every n>0, and gcd(u(a),u(b))=u(gcd(a,b)) whenever a,b>0. The value u(0) is arbitrary, and u(1) may be any positive integer. Put L(N)=lcm{u(d):0<d<=N}, with L(0)=1, and M(t)=sum_{0<m<=t} mu(m), where mu is the ordinary Moebius function. For every natural N>=0, the displayed identity holds. All quotients N/d in the cutoff are natural division; every supported d is positive.

The proof constructs the positive natural quotient A(n)=L(n)/L(n-1), for n>0, using exact divisibility of consecutive prefix lcms. Its live induction proves gcd(u(n),L(K))=product_{0<d<=K,d|n} A(d), simultaneously for every n>0. When K+1 does not divide n, the positive index gcd(n,K+1) is at most K; its u-value is already in the previous prefix and the gcd does not increase. When K+1 divides n, strong divisibility gives u(K+1)|u(n). Gcd/lcm distributivity, the gcd-times-lcm identity and cancellation of positive natural factors show that the gcd acquires exactly the factor A(K+1). The distributor is reused from its original repository source, FiniteCompatibleCrt.

At K=n, the projection reconstructs u(n)=product_{d|n} A(d). A separate telescope gives L(N)=product_{0<d<=N} A(d), including N=0. Taking logarithms of positive finite products and applying Mathlib's additive Moebius inversion gives log A(n)=(mu*logU)(n) for n>0. The arithmetic function logU is defined to vanish at zero and equals log u(n) for positive n, so no hypothesis on u(0) enters. Mathlib's finite summatory Dirichlet convolution identity then yields the exact dilation formula.

Nowicki's Strong divisibility and lcm-sequences, Theorem 2.1, PDF p. 4, attests the classical divisor reconstruction from successive prefix-lcm quotients in a gcd-domain, with equalities up to units. Positive natural values remove unit ambiguity. The logarithmic Mertens formula is a classical consequence of that reconstruction and Moebius inversion; the paper does not literally display this formula. The projection induction is independently implemented in Lean here. No mathematical originality or resolution of the remaining Robin or Riemann-hypothesis problem is claimed.

For N=0 both sides are zero. For N=1 the formula is log u(1)=log u(1), so it preserves a positive nonunit first value. The actual identity sequence and the literal Fibonacci sequence are applications of this generic theorem; they do not add retained public wrappers to this module.

## References

- Truth anchor: `D5/S3/Arith/StrongDivisibilityLcmMertens.log_prefix_lcm_eq_mertens_dilation`
- Dependency: [D5/S3/Factorization/PrimePowers/FiniteCompatibleCrt](../Factorization/PrimePowers/FiniteCompatibleCrt.md)
