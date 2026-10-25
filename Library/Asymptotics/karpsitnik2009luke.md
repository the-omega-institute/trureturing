---
bibkey: karpsitnik2009luke
authors: D. Karp and S. M. Sitnik
year: 2009
title: Inequalities and monotonicity of ratios for generalized hypergeometric function
doi: 10.1016/j.jat.2008.10.002
arxiv: math/0703084
url: https://arxiv.org/abs/math/0703084
claim: "Conjecture 1 extends the Luke lower bound of Theorem 3 to all positive sigma with positive sum of denominator-minus-numerator parameters."
strata_touched:
  - D5/S3/Analytic/KarpSitnikLuke/Result
license: citation-only
triage: anchor
---

# The conjectured sum-condition Luke lower bound

## Verified locator

https://arxiv.org/abs/math/0703084

Version: https://arxiv.org/abs/math/0703084v2.
DOI: 10.1016/j.jat.2008.10.002.
Journal of Approximation Theory 161 (2009), 337–352.
Page numbers below are printed pages of the arXiv version.

## Source statements

Theorem 3, printed p. 6, equation (23):

> For bₖ > aₖ > 0, k = 1, . . . , q, x > −1 and σ ≥ 1 the inequality
>
> $\displaystyle\frac{1}{(1+x\prod_{i=1}^q(a_i/b_i))^\sigma}<{}_{q+1}F_q(\sigma,(a_q);(b_q);-x)$
>
> holds true.

Conjecture 1, printed p. 14:

> Theorem 3 is true for all σ > 0 and ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0.

Equation (1), printed p. 1, defines the function as

$$ {}_{q+1}F_q((a_{q+1});(b_q);z)
=\sum_{n=0}^{\infty}\frac{(a_1)_n\cdots(a_{q+1})_n}
{(b_1)_n\cdots(b_q)_n n!}z^n. $$

The following sentence reads:

> where (a_q) = a₁, a₂, . . . , a_q is the parameter list and (a)ₙ = a(a + 1) · · · (a + n − 1) is the shifted factorial. The series converges for |z| < 1 and can be analytically continued onto the entire complex plane cut along [1, ∞].

## Mathematical correspondence

`hyperTerm` uses the existing `TwoBlockResult.pochRatio` for the products
of rising factorials, adds the upper parameter σ and the n! denominator,
and multiplies by zⁿ. `hyper` is its real tsum.
`claim` restricts the conjecture to −1<x<1, summable defining series and
a positive base for `Real.rpow`. This weaker assertion is already false.
The witness has q=2, σ=1, a=(1,1), b=(1/10,2), x=1/10, with sum(b−a)=1/10
and product(a/b)=5. The series is at most 37/66, less than the proposed
lower bound 2/3. It fails the componentwise hypothesis of Theorem 3.

The remaining componentwise case 0<σ<1 and Conjecture 2 are not settled
by this fixed-parameter result. The bounded literature scope is given in
`Problems/karp-sitnik-2009-luke-lower-bound.md`.
