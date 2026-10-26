---
bibkey: boudabsasimon2021kilbassaigo
authors: L. Boudabsa and T. Simon
year: 2021
title: "Some properties of the Kilbas–Saigo function"
doi: 10.3390/math9030217
url: https://arxiv.org/abs/2012.05666
claim: "Conjecture 4.5 gives two-sided hyperbolic bounds on the negative half-line for 0 < alpha <= 1, m > 0 and l > m - 1/alpha."
strata_touched:
  - D5/S3/Analytic/KilbasSaigo/Defs
  - D5/S3/Analytic/KilbasSaigo/Result
license: citation-only
triage: anchor
---

# Kilbas–Saigo hyperbolic bounds

## Verified locator

DOI: 10.3390/math9030217

Source: https://arxiv.org/abs/2012.05666

Pinned version: https://arxiv.org/abs/2012.05666v1, §4.1,
Conjecture 4.5. The journal version is *Mathematics* 9(3) (2021),
217, where the statement is Conjecture 4.

## Mathematical correspondence

The defining series is

$$E_{\alpha,m,l}(z)=\sum_{n=0}^{\infty}c_nz^n,\qquad
c_n=\prod_{k=0}^{n-1}
\frac{\Gamma(1+\alpha(km+l))}{\Gamma(1+\alpha(km+l+1))},\quad c_0=1.$$

For $0<\alpha\le1$, $m>0$, $l>m-1/\alpha$ and $x\ge0$, the statement is

$$\frac{1}{1+\frac{\Gamma(1+\alpha(l-m))}{\Gamma(1+\alpha(l-m+1))}x}
\le E_{\alpha,m,l}(-x)\le
\frac{1}{1+\frac{\Gamma(1+\alpha l)}{\Gamma(1+\alpha(1+l))}x}.$$

`Defs.ksCoeff`, `Defs.kilbasSaigo` and `Defs.claim` in
`D5/S3/Analytic/KilbasSaigo/Defs` encode exactly these objects.
`D5/S3/Analytic/KilbasSaigo/Result.result` proves the displayed bounds
with the complete parameter range. The source records $l=m-1$ and $m=1$
as known cases. The boundary $l=m-1/\alpha$ belongs to the distinct
Conjecture 3.7 in the pinned preprint.

The bounded literature scope and its limitations are stated in
`Problems/boudabsa-simon-2021-kilbas-saigo-hyperbolic-bounds.md`.
