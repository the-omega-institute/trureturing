---
bibkey: bakerharmanpintz2001primegaps
authors: R. C. Baker, G. Harman and J. Pintz
year: 2001
title: The Difference Between Consecutive Primes, II
doi: 10.1112/plms/83.3.532
url: https://doi.org/10.1112/plms/83.3.532
claim: Theorem 1 supplies a prime in every sufficiently large backward interval of length x^0.525. Its forward endpoint conversion bounds repeated actual-core label weight; it does not supply asymptotic prime counts, selected-source clock control or signed zero-head cancellation.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime existence and actual-core residence

The primary is Baker--Harman--Pintz, *The Difference Between Consecutive
Primes, II*, Proceedings of the London Mathematical Society (3) 83
(2001), 532--562, [DOI 10.1112/plms/83.3.532](https://doi.org/10.1112/plms/83.3.532).
Theorem 1 on printed p.532 was read in the
[primary article PDF hosted by the University of Maryland](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/BakerHarmanPintz.pdf),
with its interval direction and exponent checked on the rendered page.
This note cites the article rather than redistributing it. The complete
sieve proof was not independently audited or Lean-verified here.

## The original interval and the required parameter conversion

Write $\vartheta=0.525=21/40$. Theorem 1 states that, for all $x>x_0$,

$$
[x-x^\vartheta,x]\quad\text{contains prime numbers}.
$$

The statement following the theorem says that $x_0$ could be determined
effectively with enough effort; the article's theorem supplies no numerical
value for the start used here.

For the forward consumer set $y=x+2x^\vartheta$. Since $\vartheta<1$,
$y/x\to1$ and $y^\vartheta<2x^\vartheta$ for every sufficiently large
real $x$. Applying the original theorem at this $y$ gives a prime $q$ with

$$
x<y-y^\vartheta\le q\le y=x+2x^\vartheta.
\tag{BHP-F}
$$

This is an endpoint conversion of the cited theorem, not a new prime-gap
estimate. In particular the left inequality is strict, including when
$x$ itself is prime. Only existence is used; no asymptotic formula for
$\pi(x+h)-\pi(x)$ is inferred from the theorem's statement.

## The actual consumer and its boundary

The [original selector application](../Estimation/trureturing2026pricegapconvexity.md#prime-existence-bounds-the-weight-of-each-actual-core)
keeps every actual label, maximizing tie and outgoing logarithmic label
weight. It combines BHP-F with the already established first-layer
activation clock $a_{q,1}\in(q,q+1)$ and the existing all-choice strict
inventory order. A constant actual core cannot remain active across that
activation. The resulting bound concerns residence weight of that core
in the original full window, rather than the mere existence of one
unchanged-core edge.

The [Guth--Maynard note](guthmaynard2024largevalues.md) supplies a different
contract: uniform asymptotic prime counts in its stated longer intervals.
BHP-F can be used when only prime existence is required; it does not
replace the prime-count supplier elsewhere. This note makes no claim
that the exponent is the latest record. Neither prime existence nor the
residence bound proves a favorable signed zero-head estimate or Robin/RH.
