---
bibkey: ghosh2026erdos
authors: S. Ghosh; K. Ramachandran
year: 2026
title: "A note on the Erdős minimal area problem"
doi: 10.1090/proc/17897
url: https://arxiv.org/abs/2604.03036v3
claim: "The question after Proposition 3.6 asks whether Fekete polynomials minimize unit-lemniscate area when the compact set containing their zeros is connected."
strata_touched: []
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1090/proc/17897

Source: https://arxiv.org/abs/2604.03036v3

Section 1 defines the monic degree-n class with zeros in a compact set,
the unit lemniscate, and its minimal area. Theorem 3.1 gives asymptotic
optimality on the logarithmic scale for capacity greater than one.
The paragraph immediately after Proposition 3.6 states the connected-set
question. The DOI and arXiv version identify the paper; the quoted question
and its setting are supplied source text, without an independent online
locator check here.

# Fekete polynomials and minimal lemniscate area

The paragraph after Proposition 3.6 states verbatim:

> While the above proposition proves that Fekete polynomials are not area minimizers in general, it would be of interest to know if they are minimzers when the set $K$ is connected. We leave this as an open question.

For compact $K\subseteq\mathbb C$, let $P_n(K)$ be the monic polynomials
of degree $n$ with every zero in $K$. The unit lemniscate is
$\Lambda_p=\{z:|p(z)|<1\}$, and
$A_n(K)=\inf_{p\in P_n(K)}m(\Lambda_p)$, where $m$ is planar Lebesgue
measure. A Fekete tuple maximizes the product of pairwise distances among
$n$ points of $K$; its associated polynomial is the product of the monic
linear factors at those points.

The repository's `claim` asks that every such polynomial have area no
greater than every competitor in $P_n(K)$, for each compact connected $K$
and every $n\geq1$. This is the exact-minimization interpretation of the
question, rather than a logarithmic asymptotic statement.

On $K=[-20,20]$, the Fekete roots $\pm20,\pm\sqrt{80}$ give
$F(z)=(z^2-400)(z^2-80)$. The competitor
$G(z)=(z^2-400)(z^2-100)$ has all four roots in the same interval.
Disjoint discs inside $\Lambda_F$ and a disc cover of $\Lambda_G$ certify
$m(\Lambda_G)<m(\Lambda_F)$. Connectedness therefore does not suffice
for exact optimality. This finite counterexample leaves the paper's
logarithmic asymptotic optimality theorem intact.

Citation only; no source PDF or TeX is redistributed.
