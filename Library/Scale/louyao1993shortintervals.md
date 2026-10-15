---
bibkey: louyao1993shortintervals
authors: Shituo Lou and Qi Yao
year: 1993
title: The Number of Primes in a Short Interval
doi: 10.46298/hrj.1993.127
url: https://hrj.episciences.org/127
claim: Records the printed 0.99 and 1.01 count; the current Robin application instead adopts an independent BHP source above eleven twentieths.
strata_touched: []
license: citation-only
triage: anchor
---

# Printed near-unit bounds and the independent adopted supplier

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
For comparison, a fixed $11/20<s<\omega\le17/30<7/12$ lies
inside the printed range. No value at $s=11/20$, moving-exponent theorem,
exceptional-centre selection or RH premise is used.

The full external analytic proof and its computations are not
independently audited or Lean-verified. No numerical common start,
strongest-available-result or originality claim is made.
The [BHP 1997 primary](bakerharmanpintz1997goldbach.md), printed
p.4, reports serious errors in a Lou--Yao paper listed as [19].
The inspected excerpt does not include the bibliography needed to
bind that reference to an exact title and year. This warning is not
a proof that the displayed statement is false. Its analytic proof
and applicability remain unverified here, and the current
[actual-source consumer](../Estimation/trureturing2026pricegapconvexity.md#independent-two-sided-counts-above-the-strict-eleven-twentieths-cut)
does not rely on it. The independent BHP theorem supplies the
near-unit constants above strict $11/20$; the shorter region uses
Iwaniec's upper capacity and BHP 2001's terminal lower envelope.
