---
bibkey: karpsitnik2009luke
authors: D. Karp and S. M. Sitnik
year: 2009
title: Inequalities and monotonicity of ratios for generalized hypergeometric function
doi: 10.1016/j.jat.2008.10.002
url: https://arxiv.org/abs/math/0703084
claim: "Conjectures 1 and 2 propose Luke lower and upper bounds under a positive sum of denominator-minus-numerator parameters."
strata_touched:
  - D5/S3/Analytic/KarpSitnikLuke/Result
  - D5/S3/Analytic/KarpSitnikLuke/UpperResult
license: citation-only
triage: anchor
---

# The conjectured sum-condition Luke bounds

## Verified locator

https://arxiv.org/abs/math/0703084

arXiv: math/0703084. Version: https://arxiv.org/abs/math/0703084v2.
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

## Conjectured upper bound

Conjecture 2, printed p. 14, equation (38):

> For 0 < σ ≤ min(a₁, a₂, . . . , a_q), ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0 and x > 0:
>
> $\displaystyle {}_{q+1}F_q(\sigma,(a_q);(b_q);-x)<\frac{1}{\left[1+x\prod_{i=1}^q\frac{\Gamma(a_i)\Gamma(b_i-\sigma)}{\Gamma(b_i)\Gamma(a_i-\sigma)}\right]^\sigma}.\qquad (38)$

The preceding sentence reads:

> The asymptotic formula (16) and numerical experiments suggest the following

Formula (16), printed p. 5, is preceded by:

> It follows that for σ < min(a₁, a₂, . . . , a_q) we will have

$$ {}_{q+1}F_q(\sigma,(a_q);(b_q);-z)
=\frac{\prod_i\Gamma(a_i-\sigma)\Gamma(b_i)}
{\prod_i\Gamma(a_i)\Gamma(b_i-\sigma)}z^{-\sigma}
+o(z^{-\sigma}),\qquad z\to\infty. $$

The quotation transcribes the extracted display, which places a $\sigma$
next to the Gamma product. Write
$K=\prod_{i=1}^q\Gamma(a_i)\Gamma(b_i-\sigma)/(\Gamma(b_i)\Gamma(a_i-\sigma))$.
Separately, the asymptotically precise reading via (16) is
$1/(1+xK^{1/\sigma})^\sigma$: the inner exponent $1/\sigma$
makes its leading asymptotic coefficient agree with (16).
The counterexample has $\sigma=1$, where both readings coincide.

`UpperResult.claim` uses the existing `Result.hyperTerm` and `Result.hyper`,
restricts to $0<x<1$, and assumes summability and $K>0$.
Each restriction weakens the universal assertion. At
$q=2$, $\sigma=1$, $a=(2,2)$, $b=(3/2,3)$, $x=1/2$,
the Gamma recurrence gives $K=1$. The six-term alternating lower bracket
is $249826/363825>2/3$, refuting the proposed upper bound.
The componentwise upper-bound case $b_k>a_k$ is open here;
`Problems/karp-sitnik-2009-luke-upper-bound.md` specifies the scope.
