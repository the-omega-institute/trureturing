---
bibkey: karpsitnik2010logconvexity
authors: D. Karp and S. M. Sitnik
year: 2010
title: Log-convexity and log-concavity of hypergeometric-like functions
doi: 10.1016/j.jmaa.2009.10.057
url: https://arxiv.org/abs/0902.3073
claim: "The unnumbered Conjecture after Theorem 4 asks for monotonicity and exact ranges of the shifted upper-parameter Kummer ratio in inequalities (10) and (11)."
strata_touched:
  - D5/S3/Analytic/KummerRatio/Result
license: citation-only
triage: anchor
---

# Shifted upper-parameter Kummer ratios

## Verified locator

DOI: 10.1016/j.jmaa.2009.10.057

Source: https://arxiv.org/abs/0902.3073

Pinned version: https://arxiv.org/abs/0902.3073v1, the unnumbered
Conjecture after Theorem 4, inequalities (10) and (11).
Journal publication: *Journal of Mathematical Analysis and Applications*
364(2) (2010), 384–394.

## Mathematical correspondence

The source function is

$$M(s;c;x)={}_1F_1(s;c;x)
=\sum_{n\ge0}\frac{(s)_n}{(c)_n n!}x^n,$$

with ascending Pochhammer symbols. The ratio is

$$R(x)=\frac{M(b+\delta;c;x)M(a;c;x)}
 {M(a+\delta;c;x)M(b;c;x)}.$$

For $c,\delta>0$ and $0<a<b$, the formal image on the positive ray is
$(A,1)$, where
$A=\Gamma(a+\delta)\Gamma(b)/(\Gamma(b+\delta)\Gamma(a))$.
The printed phrase “onto (1, A)” lists the limiting values in the order
$x\to0^+$ and $x\to+\infty$; the increasing order of the interval endpoints
is $(A,1)$. For $a<b<c-\delta$, the negative-ray image is $(B,1)$, where
$B=\Gamma(c-a-\delta)\Gamma(c-b)/
(\Gamma(c-b-\delta)\Gamma(c-a))$.

`Defs.kummerCoeff`, `Defs.kummer`, `Defs.ratio` and `Defs.claim` in
`D5/S3/Analytic/KummerRatio/Defs` encode these source objects.
`D5/S3/Analytic/KummerRatio/Result.result` proves both strict monotonicity
statements and both exact images with all the displayed parameter ranges.

The bounded literature scope and its limitations are stated in
`Problems/karp-sitnik-2010-kummer-ratio-monotonicity.md`.
Exhaustive literature completeness and priority are ASSUMED-UNVERIFIED.
