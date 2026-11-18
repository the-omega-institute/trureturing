---
bibkey: nist2026dlmfpfaff
authors: NIST Digital Library of Mathematical Functions
year: 2026
title: "Pfaff transformation and complete elliptic integral connection formulas"
doi: null
url: https://dlmf.nist.gov/15.8.E1
claim: "The principal half-binomial period has the Pfaff square-root multiplier, and its complementary period ratio has opposite unit jumps on the two half-planes."
strata_touched:
  - D5/S3/Analytic/OriginalHalfBinomialSlitPeriod
  - D5/S3/Analytic/OriginalHalfBinomialPfaffNome
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

For nonreal $r$, take the principal moduli $k=\sqrt r$ and
$k'=\sqrt{1-r}$. The complete-integral connection formulas are

$$
K(ik/k')=k'K(k),\qquad
K(1/k')=k'\bigl(K(k')\pm iK(k)\bigr).
$$

DLMF requires $\operatorname{Re} k>0$ for 19.7.3, which holds for
this principal $k$. The upper sign applies for $\operatorname{Im}(k^2)>0$
and the lower sign for $\operatorname{Im}(k^2)<0$. DLMF credits this sign
distinction to H. E. Fettis (1970).
[DLMF 19.7.2a](https://dlmf.nist.gov/19.7.E2a.tex),
[DLMF 19.7.3b and sign convention](https://dlmf.nist.gov/19.7#E3),
[Fettis bibliography entry](https://dlmf.nist.gov/bib/F#bib784)

The squared transformed moduli are $r/(r-1)$ and $1/(1-r)$. The
principal complete integral is even in its modulus, so taking $i$ times
the complementary-to-direct quotient gives
$\tau(r/(r-1))=\tau(r)\mp1$ with the same half-plane convention.
[DLMF §19.2(ii)](https://dlmf.nist.gov/19.2.ii)
