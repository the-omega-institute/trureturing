---
bibkey: dimitrov2026c4c5
authors: S. I. Dimitrov
year: 2026
title: "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
doi: null
url: https://arxiv.org/abs/2606.12484v1
claim: "Conjectures 4 and 5 assert the displayed reciprocal-product lower bounds for every integer n ≥ 2 and k ≥ 1, with φ Euler's totient, ψ Dedekind's function, and σ the positive-divisor sum."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5
license: source-reference
triage: anchor
---

# Dimitrov's reciprocal-product lower bounds

S. I. Dimitrov's arXiv:2606.12484v1, §2 (PDF p.4), states two conjectures for every integer
$n\ge2$ and $k\ge1$. The functions are Euler's totient $\varphi(n)$, Dedekind's
$\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$, and the positive-divisor sum
$\sigma(n)=\sum_{d\mid n}d$. Powers in both source expressions are pointwise powers of
function values.

Conjecture 4 is the reciprocal product of
$\varphi(n)^k(\psi(n)+\sigma(n))$,
$\psi(n)^k(\varphi(n)+\sigma(n))$, and
$\sigma(n)^k(\varphi(n)+\psi(n))$, bounded below by
\[
\frac{5n(n+1)^{k-1}(n-1)^k+2(n-1)^{2k}+2n^2(n+1)^{2k-2}}
{n(n+1)^{k-1}(n-1)^k}.
\]
Conjecture 5 replaces each mixed sum by the sum of the corresponding pointwise powers
and has right side
\[
\frac{10(n-1)^{2k}+7(n^2-1)^k+(n+1)^{2k}}
{(n-1)^{2k}+(n^2-1)^k}.
\]

The D5 module proves both complete statements. Its native bridge establishes
$0<\varphi(n)\le n-1<n+1\le\psi(n)\le\sigma(n)$; the remaining argument is an ordered
reciprocal-product inequality applied first to the mixed terms and then to their
pointwise-power specialization. The denominator facts use $n\ge2$ and $k\ge1$ directly.

## Verified locator

https://arxiv.org/abs/2606.12484v1, §2, PDF page 4, Conjectures 4 and 5.
