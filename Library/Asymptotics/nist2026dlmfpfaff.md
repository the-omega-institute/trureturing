---
bibkey: nist2026dlmfpfaff
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: "Hypergeometric function, Pfaff transformation"
doi: null
url: https://dlmf.nist.gov/15.8.E1
claim: "The principal half-binomial period at r/(r − 1) is the principal square root of 1 − r times the period at r on the slit plane."
strata_touched:
  - D5/S3/Analytic/OriginalHalfBinomialSlitPeriod
license: citation-only
triage: anchor
---

# Pfaff transformation for the half-binomial period

For the parameter $r=k^2$, the normalized complete elliptic integral is
$P(r)=2K(k)/\pi={}_2F_1(1/2,1/2;1;r)$. The integral and its series
normalization are given in [DLMF §19.2](https://dlmf.nist.gov/19.2) and
[DLMF 19.5.1](https://dlmf.nist.gov/19.5.E1).

The normalized hypergeometric function $\mathbf{F}$ equals the ordinary
hypergeometric function at $c=1$ since $\Gamma(1)=1$.
[DLMF 15.2.1–2](https://dlmf.nist.gov/15.2)

Setting $a=b=1/2$ and $c=1$ in the first Pfaff equality gives
$P(r)=(1-r)^{-1/2}P(r/(r-1))$. For $r\in\mathbb C\setminus[1,\infty)$,
the transformed argument lies in the same slit plane because
$1-r/(r-1)=1/(1-r)$. Multiplying by the principal square root gives
$P(r/(r-1))=(1-r)^{1/2}P(r)$. [DLMF 15.8.1](https://dlmf.nist.gov/15.8.E1)

## Verified locator

DLMF §15.8(i), equation 15.8.1, first Pfaff rearrangement, with principal
values and $a=b=1/2$, $c=1$, $z=r$. [DLMF 15.8.1](https://dlmf.nist.gov/15.8.E1)

DLMF equation 19.5.1 gives the normalization $P(r)=2K(k)/\pi$ for $r=k^2$.
[DLMF 19.5.1](https://dlmf.nist.gov/19.5.E1)
