---
bibkey: baier2016squaresieve
authors: Stephan Baier
year: 2016
title: The square sieve and the large sieve with square moduli
doi: null
url: https://arxiv.org/abs/1506.06148v2
claim: "Lemma 2 recalls Heath-Brown's weighted square sieve, retaining the Jacobi correlations and the support restriction |d|<exp(L) for L sieve primes."
strata_touched: []
license: citation-only
triage: anchor
---

# The weighted square-sieve input

The inspected primary text is [arXiv:1506.06148v2](https://arxiv.org/pdf/1506.06148v2), updated 2016-06-07; the first version was submitted 2015-06-19. The locator used here is **Lemma 2, printed p.2**, rather than the paper's main large-sieve theorem. This is an existing theorem, not a new estimate or a statement of the latest large-sieve bound.

Baier credits D. R. Heath-Brown, *The square sieve and consecutive square-free numbers*, **Mathematische Annalen 266** (1984), 251–259, Theorem 1. The lemma below was checked in Baier's primary text; this note does not claim an independent full-text inspection of Heath-Brown's article.

Let $\mathcal S$ contain $L\ge1$ distinct primes. For a nonnegative weight $w$ supported on positive integers, impose the lemma's additional restriction

$$
w(d)=0\qquad\text{if }d=0\text{ or }|d|\ge\exp(L).
$$

The weighted number of positive squares then satisfies

$$
\sum_{t\ge1}w(t^2)
\ll\frac1L\sum_{d\in\mathbb Z}w(d)
+\frac1{L^2}
\sum_{\substack{p,q\in\mathcal S\\p\ne q}}
\left|\sum_{d\in\mathbb Z}w(d)
\left(\frac d{pq}\right)\right|.
\tag{B1}
$$

The pair sum is ordered. In applications below all sieve primes are odd, so the Jacobi symbol is unambiguous. Its value at a nonunit is zero; replacing that value by one changes the correlation term. The support cap is also part of the quoted lemma. A proposed use with larger discriminants needs another justified sieve formulation or a new choice of primes before (B1) can be applied.

No Lean verification or originality claim is supplied. The primary input alone does not bound the correlations of a population selected by its own prime divisibility conditions.
