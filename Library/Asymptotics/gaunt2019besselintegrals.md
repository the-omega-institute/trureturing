---
bibkey: gaunt2019besselintegrals
authors: Robert E. Gaunt
year: 2019
title: Inequalities for some integrals involving modified Bessel functions
doi: 10.1090/proc/14433
url: https://arxiv.org/abs/1806.00524
claim: "Conjecture 2.4 asks for a sharp lower bound on a weighted modified-Bessel K tail."
strata_touched:
  - D5/S3/Analytic/GauntBesselTail/Result
license: citation-only
triage: anchor
---

# Gaunt's weighted Bessel tail conjecture

## Verified locator

https://arxiv.org/abs/1806.00524

R. E. Gaunt, *Inequalities for some integrals involving modified Bessel
functions*, Proc. Amer. Math. Soc. 147 (2019), 2937–2951,
DOI 10.1090/proc/14433. Conjecture 2.4 is on manuscript page 7 of
arXiv:1806.00524v2.

## Conjecture 2.4

The following fragments are copied from the supplied text extraction:

> Then, for all x > 0,

> We have equality in (2.17)

> in inequality (2.17) is best possible, in the sense that, for any

The last fragment ends before the extracted beta symbol; the extraction
breaks the displayed square roots and subscripts across lines. The complete
mathematical statement, with those displays reconstructed, is as follows.
For real $n<1$ and $\nu\ge1-n+\sqrt{2(1-n)}$, put

$$p=\nu+n,\qquad
\alpha_{\nu,n}=p-\sqrt{p^2-2\nu-1},\qquad
\alpha'_{\nu,n}=p+\sqrt{p^2-2\nu-1}.$$

For every $x>0$, the proposed strict inequality (2.17) is

$$\int_x^\infty t^{-\nu}K_{\nu+n}(t)\,dt
>x^{-\nu}K_{\nu+n-\alpha_{\nu,n}}(x).$$

At $n=1$ equality holds for every real $\nu$. The orders obtained from
$\alpha$ and $\alpha'$ are negatives of one another and give the same
Bessel function. For every other $\beta$, either
$x^{-\nu}K_{p-\beta}(x)<x^{-\nu}K_{p-\alpha}(x)$ for every $x>0$,
or there exists $y>0$ at which the tail is strictly smaller than
$y^{-\nu}K_{p-\beta}(y)$.

The integral representation of $K$ is recorded separately in
`D5/L/Asymptotics/nist2026dlmfbesselkintegral`, equation 10.32.9.
