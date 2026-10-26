---
bibkey: qiumaxiang2024turan
authors: S.-L. Qiu, X.-Y. Ma and X.-Y. Xiang
year: 2024
title: "Turán-type inequalities for Gaussian hypergeometric functions, and Baricz's conjecture"
doi: 10.48550/arXiv.2408.15723
url: https://arxiv.org/abs/2408.15723
claim: "Conjecture 6.2 classifies strict parameter decrease of the zero-balanced Gauss quotient in (1.6) and the shifted-parameter comparison in (1.7)."
strata_touched:
  - D5/S3/Analytic/GaussZeroBalanced/Result
license: citation-only
triage: anchor
---

# Zero-balanced Gauss quotient classifications

## Verified locator

DOI: 10.48550/arXiv.2408.15723

Source: https://arxiv.org/abs/2408.15723

Pinned version: https://arxiv.org/abs/2408.15723v1, §6,
Conjecture 6.2, inequalities (1.6) and (1.7).
The DOI identifies the arXiv record; no journal DOI is asserted.

## Mathematical correspondence

The source function is

$$F(a,b;c;x)={}_2F_1(a,b;c;x)
=\sum_{n\ge0}\frac{(a)_n(b)_n}{(c)_n n!}x^n.$$

The zero-balanced quotient is

$$Q(a,b,x)=\frac{F(a+1,b+1;a+b+1;x)}{F(a,b;a+b;x)}.$$

For every $a,b>0$, Conjecture 6.2 asserts that
$\partial_b Q(a,b,x)<0$ at every $x\in(0,1)$ exactly when
$b\le\sqrt{a(a+1)}$. For $0<a<1$, it also asserts that

$$\frac{F(a+1,2-a;2;x)}{F(a,1-a;1;x)}
>\frac{F(a+1,5/2-a;5/2;x)}{F(a,3/2-a;3/2;x)}$$

holds at every $x\in(0,1)$ exactly when $a\ge3/7$.

`Defs.gauss`, `Defs.quot`, `Defs.ineq17` and `Defs.claim` in
`D5/S3/Analytic/GaussZeroBalanced/Defs` encode these source objects.
`Defs.f` is the contiguous quotient
$F(a,b;a+b+1;x)/F(a,b;a+b;x)$ used in the comparison.
`D5/S3/Analytic/GaussZeroBalanced/Result.result` proves both clauses
with their displayed parameter ranges and strict inequalities.

The conjecture corrects Á. Baricz, *Math. Z.* 256 (2007), 895–911,
DOI 10.1007/s00209-007-0111-x, Conjecture A. The same source paper
refutes that conjecture as an unrestricted statement.

The bounded literature scope and its limitations are stated in
`Problems/qiu-ma-xiang-2024-zero-balanced-gauss-turan.md`.
Exhaustive literature completeness and priority are ASSUMED-UNVERIFIED.
