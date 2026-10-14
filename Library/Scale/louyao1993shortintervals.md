---
bibkey: louyao1993shortintervals
authors: Shituo Lou and Qi Yao
year: 1993
title: The Number of Primes in a Short Interval
doi: 10.46298/hrj.1993.127
url: https://hrj.episciences.org/127
claim: A later published two-sided count gives smaller fixed local allowances on the original Robin lag region strictly above eleven twentieths.
strata_touched: []
license: citation-only
triage: anchor
---

# Reuse the later two-sided bounds in their stated range

The primary is *The Number of Primes in a Short Interval*,
*Hardy--Ramanujan Journal* **16** (1993), 21--43,
[DOI 10.46298/hrj.1993.127](https://doi.org/10.46298/hrj.1993.127).
The inspected [journal PDF](https://hrj.episciences.org/127/pdf)
has SHA-256
`73f2be6816e3564f21195ec12ce028b4d44cba29b641575f57d7faefc7150c78`.

Theorem 3, printed p.25, equations (1.20)--(1.21), states that for
all sufficiently large $x$, uniformly for $11/20<s\le7/12$,

$$
0.99\frac{x^s}{\log x}
\le\pi(x)-\pi(x-x^s)
\le1.01\frac{x^s}{\log x}.
$$

The constants are the printed $0.99$ and $1.01$, respectively.
The project chooses
only fixed $11/20<s<\omega\le17/30<7/12$ before taking one common
source start. No value at $s=11/20$, moving-exponent theorem,
exceptional-centre selection or RH premise is used.

The full external analytic proof and its computations are not
independently audited or Lean-verified. No numerical common start,
strongest-available-result or originality claim is made.
The [existing actual-source transfer](../Estimation/trureturing2026pricegapconvexity.md#a-near-unit-two-sided-stock-bound-above-the-strict-six-elevenths-cut)
is reused with these two constants; it retains the same complete
strict measure, prime weights, incomplete-block costs and integer
competitor. Its resulting stock root is a project application,
not an external prime theorem or a new generic root calculation.
