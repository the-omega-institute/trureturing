---
bibkey: inoue2019mobiuszeta
authors: Shōta Inoue
year: 2019
title: Relations among some conjectures on the Möbius function and the Riemann zeta-function
doi: 10.4064/aa170622-16-10
url: https://arxiv.org/abs/1705.00853v2
claim: Lemma 1 reproduces an unconditional reciprocal-zeta good-height theorem; its subpower horizontal bound pays the raw full-residue odd-source annulus error without an additional growing-height premise, while leaving the signed Robin estimate unresolved.
strata_touched: []
license: citation-only
triage: anchor
---

# Published good heights for the reciprocal zeta function

The published paper is Shōta Inoue, *Acta Arithmetica* **191** (2019),
1–32, [DOI](https://doi.org/10.4064/aa170622-16-10). The inspected
author version is [arXiv:1705.00853v2](https://arxiv.org/pdf/1705.00853v2),
revised 22 June 2017. The arXiv record inspected on 10 October 2026 lists
v2 as its latest version. Its PDF has 26 pages and SHA-256
`0cdbc0b10e26922337c892a46a2f096df52b9d179dfecb8b9356d47c0ab11a98`.
The journal identification was checked against Crossref; the manuscript's
Lemma 1, PDF p.10, was also checked against its
[HTML TeX](https://arxiv.org/html/1705.00853v2#Thmlemma1).
The cited original proof and the complete paper were not independently
audited. No Lean verification is supplied.

## The exact unconditional supplier

Lemma 1 attributes the following result to K. Ramachandra and
A. Sankaranarayanan, *Notes on the Riemann zeta-function*,
*Journal of the Indian Mathematical Society* **57** (1991), 67–77,
Theorem 2. There are absolute constants $C>0$ and $U_0$ such that,
for every real $U\ge U_0$,

$$
\min_{U\le T\le U+U^{1/3}}
\max_{1/2\le r\le2}|\zeta(r+iT)|^{-1}
\le \exp\!\left[C(\log\log U)^2\right].
\tag{IH1}
$$

The maximum is over the whole closed real-part interval at the same
height. There is no RH or simple-zero hypothesis. The next lemma in
the manuscript does assume RH; that distinct result is not used here.
In particular the selected heights satisfy a bound
$\ll_\varepsilon T^\varepsilon$ for every fixed $\varepsilon>0$.
The statement supplies neither numerical values for $C,U_0$ nor a
certified finite list of these heights.

## Extension to the horizontal contour used by the existing application

For such a selected $T$, let

$$
C_T=\sup_{r\le1,\ \xi\in\{-1,1\}}
|\zeta(r+i\xi T)|^{-1}.
$$

The functional-equation bounds in Lemma B.1 of
[Chirre–Helfgott](chirrehelfgott2025bounded.md) extend (IH1) to

$$
C_T\ll_\varepsilon T^\varepsilon.
\tag{IH2}
$$

To check the whole contour, split its real parts into $[1/2,1]$,
$[-1,1/2]$ and $(-\infty,-1]$. The first interval is contained in
(IH1). On the second, reflection sends $r$ to $1-r\in[1/2,2]$;
the functional-equation prefactor is bounded for large $T$ since
$1/2-r\ge0$. Indeed the source's (B.1) contains the factor
$(2\pi e/|1-r-iT|)^{1/2-r}$ and
$e^{\pi T/2}/(2|\sin(\pi(r+iT)/2)|)$, respectively at most one
and uniformly bounded when $T$ is large. On the third, (B.2) and
$|1/\zeta(1-r-iT)|\le\zeta(1-r)\le\zeta(2)$ give a uniform
$O(T^{-3/2})$ bound. Conjugation supplies the same estimates at $-T$.
This uses existing functional-equation estimates, not a new
reciprocal-zeta theorem or a strengthening of (IH1).

Taking $U=x^{3/4}$ gives an available height in
$[x^{3/4},x^{3/4}+x^{1/4}]$ for every sufficiently large real $x$.
The [raw full-residue application](chirrehelfgott2025bounded.md#published-good-heights-pay-the-raw-critical-annulus)
uses (IH2) to pay the actual odd-source annulus at the critical scale.
It needs no additional mathematical assumption that such heights exist.
It does not infer the stronger certificate $C_T\le(\log x)^2$,
identify a numerical starting point, certify interior residue evaluation,
or supply the signed finite-head/core lower bound for Robin.

The existing repository good-height declarations for the completed-zeta
explicit formula control the logarithmic derivative. That different
bound is not substituted for (IH1)'s reciprocal-zeta bound. The present
source is reused as a paper input; no duplicate good-height construction
or new Lean declaration is introduced.
