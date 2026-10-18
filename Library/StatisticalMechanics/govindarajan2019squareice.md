---
bibkey: govindarajan2019squareice
authors: Suresh Govindarajan; Anthony J. Guttmann; Varsha Subramanyan
year: 2019
title: "On a square-ice analogue of plane partitions"
doi: 10.4171/AIHPD/67
url: https://arxiv.org/abs/1607.01890v1
claim: "For width l, a height function h on Z^2 agrees with h_0^(l) at all but finitely many sites, satisfies h >= h_0^(l) and the ice rule |h(u) - h(v)| = 1 on adjacent sites; its volume is the sum of (h - h_0^(l))/2, and a_l(n) is the number of height functions of volume n. From fits to exact data the paper conjectures a_l(5) = C(l,5) + 10 C(l,3) - 2 C(l,2) + 36 l - 14 for l >= 3, with similar formulas for n <= 9; the cases n = 2, 3, 4 are stated as proved."
strata_touched:
  - D5/S3/StatisticalMechanics/SquareIceFiveOrangeCount
license: citation-only
triage: anchor
---

# On a square-ice analogue of plane partitions

Suresh Govindarajan, Anthony J. Guttmann, Varsha Subramanyan, Ann. Inst.
Henri Poincaré D 6, 123–154 (2019), arXiv:1607.01890v1 (cond-mat.stat-mech).
Quotations are from the arXiv v1 TeX source; the published version keeps the
same text.

The reference configuration and height functions:

> Let $v=(x,y)\in \mathbb{Z}^2$ and for fixed $\ell=1,2,3,\ldots$, following \cite{Propp2014} define $h^{(\ell)}_0(v)=\begin{cases} |x|+|y| & x<0 \\ |x+y| & 0\leq x < \ell\\ |y+\ell -1| + |x-\ell+1| & x\geq \ell \end{cases}$.
> The \textit{height} function $h$ on $\mathbb{Z}^2$ is an integer-valued function that agrees with $h^{(\ell)}_0$ almost everywhere (i.e., at all but finitely many places), is greater than or equal to $h^{(\ell)}_0$ everywhere, and satisfies the condition that if $u$ and $v$ are adjacent locations in $\mathbb{Z}^2$, $|h(u)-h(v)|=1$. The last condition is called the \textit{ice rule}.

The volume and the counts:

> Define the volume of the height function as follows: $n:=\sum_{(x,y)\in \mathbb{Z}^2} \frac12 \left(h(x,y)-h^{(\ell)}_0(x,y)\right)$.
> Let $a_\ell(n)$ denote the number of height functions with volume $n$ for an initial configuration of width $\ell$.

The fixed-volume formulas:

> Using code which, for fixed $\ell$, generates the first few numbers in $a_\ell(n),$ enables us to conjecture the following using fits to the data: … $a_\ell(5) =\binom{\ell}5+ 10 \binom{\ell}3 -2\binom{\ell}2+36\ell -14 \text{ for }\ell\geq 3$ …
> For $n=2,3,4$, the formulae have been proved \cite{VarshaThesis}. … For $5\leq n\leq 9$, the above formulae have been checked to be consistent with exact numbers given in Table 2 for $\ell\leq 20$.

The paper also states the general Conjecture 2.2: for fixed $n$ and $\ell \ge \lceil n/2 \rceil$, $a_\ell(n)$ is a polynomial of degree $n$ in $\ell$ of a prescribed binomial form.

## Verified locator

- DOI: https://doi.org/10.4171/AIHPD/67 (Ann. Inst. Henri Poincaré D 6
  (2019), 123–154; the published text, §2.3, keeps the formula as a
  conjecture).
- URL: https://arxiv.org/abs/1607.01890v1 (v1, 2016-07-07, the only
  version; source `paperv1.tex`, md5 `38365b16e0fc75dcc1eb9aea26233fb9`):
  the definitions (l. 96–115), the fixed-volume formulas (l. 305–316) and
  Conjecture 2.2 (l. 318–323).
