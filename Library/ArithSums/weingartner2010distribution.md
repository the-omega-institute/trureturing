---
bibkey: weingartner2010distribution
authors: Andreas Weingartner
year: 2010
title: The distribution functions of σ(n)/n and n/φ(n), II
doi: null
url: https://arxiv.org/abs/1011.4262v1
claim: "Equation (5) identifies the moment Euler product W(s); Lemma 5 gives its large-positive-moment expansion with b₂=π²/6. A nonnegative divisor expansion yields a finite bound Σ_{n≤X}(n/φ(n))^s≤XW(s), and hence a deterministic subpolynomial count of possible Robin failures in bounded-ratio intervals."
strata_touched: []
license: citation-only
triage: anchor
---

# Weingartner 2010: abundancy distribution and finite positive moments

Andreas Weingartner, *The distribution functions of σ(n)/n and n/φ(n), II*,
author preprint, arXiv:1011.4262v1 (2010). This card pins the author version;
it does not assert a journal DOI or a later publication year.

## Original statements used

Equation (5) defines

$$
W(s)=\prod_p\left(1+\frac{(1-p^{-1})^{-s}-1}{p}\right)
=\lim_{N\to\infty}\frac1N\sum_{n\le N}(n/\varphi(n))^s.
$$

The paper states this identity for complex $s$. The present application
uses only positive real $s$ and the Euler product.

Lemma 5 assumes $s\ge e$ and defines $z$ by $s=z\log z$. For each fixed
integer $m\ge2$, it gives the asymptotic expansion, as $z\to\infty$,

$$
\log W(s)=s\log(e^\gamma\log z)-z+
 z\sum_{j=2}^m\frac{b_j}{(\log z)^j}
 +O_m\left(\frac z{(\log z)^{m+1}}\right),
\qquad b_2=\frac{\pi^2}{6}.
$$

Lemma 6 treats $t\ge1$, $y=e^{t e^{-\gamma}}$, and
$\min_{s\ge e}W(s)t^{-s}$; its first correction is likewise
$(\pi^2/6)y/\log^2y$. Lemma 5 with an explicit moment already suffices for
the finite application below, so no minimizer is required there.

## Finite bridge and precise application

For each real $s>0$, define the nonnegative multiplicative function
$a_s$ by $a_s(p)=(1-p^{-1})^{-s}-1$, $a_s(p^k)=0$ for $k\ge2$, and
$a_s(1)=1$. Then

$$
(n/\varphi(n))^s=\sum_{d\mid n}a_s(d),\qquad
\sum_{d\ge1}\frac{a_s(d)}d=W(s).
$$

The latter series converges since $a_s(p)=O_s(1/p)$. Consequently, for
every finite real $X\ge1$ and every real $s>0$,

$$
\sum_{n\le X}(n/\varphi(n))^s
=\sum_{d\le X}a_s(d)\lfloor X/d\rfloor\le XW(s).
$$

This pointwise-in-$(X,s)$ argument permits a growing moment without
interchanging the paper's fixed-moment average limit. Since
$Z(n)=\sigma(n)/n\le n/\varphi(n)$, it gives

$$
\#\{n\le X:Z(n)\ge t\}\le XW(s)t^{-s}.
$$

For $A\to\infty$, $X\ge A$, set $t=e^\gamma\log\log A$,
$y=\log A$, and $s=y\log y$. Lemma 5 with $m=2$ yields

$$
\begin{aligned}
&\#\{A\le n\le X:Z(n)\ge e^\gamma\log\log n\}\\
&\quad\le\exp\left(
\log(X/A)+\frac{\pi^2}{6}\frac{\log A}{(\log\log A)^2}
+O\left(\frac{\log A}{(\log\log A)^3}\right)\right).
\end{aligned}
$$

For bounded $X/A$, this is
$\exp((\pi^2/6+o(1))\log X/(\log\log X)^2)$.
The inequality includes the threshold equality. It bounds actual
potential Robin violations, not every integer surviving an unrelated
necessary-condition sieve. It does not establish that the set is empty.

## Scope

The paper's limiting distribution tails are not uniform finite estimates
for growing moduli or moving thresholds. The finite bound above comes
from the separate nonnegative expansion. It applies to all integers in
the interval and does not itself exploit Fibonacci progressions.

This is literature use and a paper derivation; no Lean statement or
kernel verification is supplied by this card. No originality claim or
complete literature-search claim is made.

## Locators

- Pinned abstract: https://arxiv.org/abs/1011.4262v1
- Pinned original PDF: https://arxiv.org/pdf/1011.4262v1
- Pinned HTML: https://arxiv.org/html/1011.4262v1
- Exact locations: equation (5), Lemma 5, Lemma 6.
