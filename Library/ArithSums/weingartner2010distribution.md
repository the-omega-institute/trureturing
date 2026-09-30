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
\qquad b_2=\frac{\pi^2}{6},\quad b_3=-\frac{\pi^2}{6}.
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

## Actual valuation moments and the comparison of tails

The proof of Lemma 5 also separates the lower and upper integrals.
Equations (13) and (14) give $q_2(k)=1/k$ and the lower integral's own
coefficient

$$
\theta_2=\sum_{k\ge1}\frac{(-1)^{k+1}}{k^2}=\frac{\pi^2}{12}.
$$

Together with the local replacement in equation (8) and the strong
Mertens/PNT estimate in equation (9), this identifies the leading
correction for the product restricted to $p\le z$, with $s=z\log z$.
The other half comes from the upper integral in equation (19).
Sections 210 and 212 use the explicitly located lower contribution in
a finite divisor construction; they do not infer an equal split merely
from the full coefficient $b_2=\pi^2/6$.

For the abundancy tail $A(t)$ and the totient tail $B(t)$ defined in the
original paper, Theorem 3 states, for sufficiently large $t$ and
$y=e^{t e^{-\gamma}}$,

$$
A(t)\le B(t)<e^{3\sqrt y}
A\left(t-\frac{5e^\gamma}{\sqrt y}\right).
$$

Both the multiplicative factor and the threshold shift are part of the
statement. They do not by themselves give a finite progression bound.
Theorem 1 gives the two tails the same expansion to every fixed order;
neither theorem says that their finite samples agree.

Section 209 of the FIB theory volume instead keeps actual valuations via
the nonnegative multiplicative coefficients
$b_s(p^a)=Z(p^a)^s-Z(p^{a-1})^s$ and the Euler product
$U(s)=\sum_d b_s(d)/d$. Its elementary comparison with $W(s)$ is a
repository paper derivation, not a quoted statement of this source.
The negative coefficient $b_3=-\pi^2/6$ above is used there to distinguish
an exact leading-order saving from a bound with an uncontrolled remainder.
This coefficient $b_3$ is the asymptotic expansion coefficient, not the
separately defined arithmetic function $b_s(d)$.

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
- Exact locations: equation (5), Lemma 5, Lemma 6, Theorems 1 and 3;
  the separate lower-integral contribution uses equations (8), (9),
  (13), (14), contrasted with (19).
