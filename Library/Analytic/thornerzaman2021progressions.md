---
bibkey: thornerzaman2021progressions
authors: Jesse Thorner and Asif Zaman
year: 2021
title: Refinements to the prime number theorem for arithmetic progressions
doi: null
url: https://arxiv.org/abs/2108.10878v2
claim: "Theorem 1.1 gives an unconditional effective weighted prime asymptotic in arithmetic progressions when lambda h/phi(q) is at least x^(theta+epsilon), retaining the exceptional real-zero alternative."
strata_touched: []
license: citation-only
triage: anchor
---

# Effective weighted prime counts in short intervals

Primary source: [arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2),
version 21 September 2021, §1.1, Theorem 1.1, printed p.1.
The statement is cited directly; no proof of the published theorem or
Lean certification is supplied by this note.

For coprime integers $q\ge2$ and $a$, and $4\le h\le x$, the theorem
defines an exceptional-zero-dependent factor $\lambda$ and exponent
$\theta$. Without the exceptional real zero they are $\lambda=1$
and $\theta=7/12$. For each fixed $0<\varepsilon<1-\theta$, if
$\lambda h/\varphi(q)\ge x^{\theta+\varepsilon}$, it gives

$$
\sum_{\substack{x-h<p\le x\\p\equiv a\pmod q}}\log p
=\frac{\lambda h}{\varphi(q)}
\left[1+O_\varepsilon\left(
\exp\left\{-\frac{c_1\log x}{
\log q+(\log(x/h))^{2/3}(\log^+\log(x/h))^{1/3}
+(\log x)^{2/5}(\log\log x)^{1/5}}\right\}\right)\right].
$$

The constant $c_1=c_1(\varepsilon)>0$ and the implied constant are
effectively computable. The first product in the denominator has its
continuous zero convention at $h=x$; $\log^+u=\max\{0,\log u\}$.
The general exceptional-zero branch must not be omitted for arbitrary
moduli.

For the Robin gap application, set $q=2$, $a=1$ and
$\varepsilon=1/60$. Modulo $2$ there is no nontrivial real character,
so the exceptional-zero branch does not occur. Hence
$\lambda=1$, $\varphi(2)=1$ and
$\theta+\varepsilon=7/12+1/60=3/5$. At large interval starts all primes
in the interval are odd, so the progression sum equals the full weighted
prime sum there.

The [owning actual-gap application](../Estimation/trureturing2026pricegapconvexity.md#weighted-short-interval-counts-pay-more-actual-gap-residuals)
uses this increment estimate with an actual endpoint contact and the
existing strict first-layer activation rule. It does not use an
increment bound to erase an arbitrary complete primitive baseline.
The theorem and this note supply neither a same-source signed future
occupation/credit bound nor a Robin or RH proof.
