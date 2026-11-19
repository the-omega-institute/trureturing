---
bibkey: dimitrov2026c6
authors: S. I. Dimitrov
year: 2026
title: "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
doi: null
url: https://arxiv.org/abs/2606.12484v1
claim: "Conjecture 6 asserts the three-term rational lower bound for every n ≥ 2 and k ≥ 1, with pointwise powers of Euler's totient, Dedekind psi and the positive-divisor sum."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovLowerBoundC6
license: source-reference
triage: anchor
---

# Dimitrov's sixth conjecture

## Locator

The exact source is [arXiv:2606.12484v1](https://arxiv.org/abs/2606.12484v1),
[Conjecture 6](https://arxiv.org/html/2606.12484v1#Thmconjecture6).

## Statement and application

With $a=\varphi(n)^k$, $b=\psi(n)^k$, and $c=\sigma(n)^k$, it asks whether

$$
\frac{ab}{c(a+b)}+\frac{ac}{b(a+c)}+\frac{bc}{a(b+c)}
\geq \frac{4(n-1)^{2k}+(n^2-1)^k+(n+1)^{2k}}
{2((n-1)^{2k}+(n^2-1)^k)}
$$

for all integers $n\geq2$, $k\geq1$. The powers are pointwise powers of function
values. Theorem 4 in the same source concerns only $k=1$; Conjecture 3 has a
different right side. Neither replaces this endpoint.

For positive $a,b,c$, set $A=a(b+c)$, $B=b(a+c)$, $C=c(a+b)$. Then

$$
(A+B+C)(A^{-1}+B^{-1}+C^{-1})
=6+2\left(\frac{ab}{c(a+b)}+\frac{ac}{b(a+c)}+\frac{bc}{a(b+c)}\right).
$$

The right side of Conjecture 5 is likewise six plus twice the right side of
Conjecture 6. Thus the complete source statement follows by exact field
normalization from the existing frozen `DimitrovLowerBoundsC4C5.result5`.
The native meanings of the three functions are unchanged.

No donor source is copied by this application. The imported Conjecture 5
development uses the modified Apache-2.0 supplier cone documented in
[dimitrov2026c4c5](dimitrov2026c4c5.md), with the complete license at
[`docs/reports/licenses/dimitrov-LICENSE.txt`](../../docs/reports/licenses/dimitrov-LICENSE.txt).
This application makes no priority or worldwide literature-exhaustiveness claim.
