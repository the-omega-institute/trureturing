---
slug: hirche-2020-cachin-renyi-concavity-alpha-ge-two
bibkey: hirche2020renyibounds
doi: null
url: https://arxiv.org/abs/2004.14408v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.result
---

# Cachin Rényi combining concavity for orders at least two

## Problem

The target is the $\alpha\ge2$ concavity clause of C. Hirche, “Rényi Bounds
on Information Combining”, ISIT 2020, arXiv:2004.14408v1, Conjecture IV.18,
with the source statement and admission scope supplied by
[#18704](https://github.com/the-omega-institute/trureturing/issues/18704).
For every real $\alpha\ge2$ and every $y\in[0,\log2]$,

$$
x\longmapsto h_\alpha(h_\alpha^{-1}(x)\star h_\alpha^{-1}(y))
$$

is concave on $[0,\log2]$, where
$h_\alpha(p)=\log(p^\alpha+(1-p)^\alpha)/(1-\alpha)$,
$p\star q=p+q-2pq$, and the inverse branch has probability domain $[0,1/2]$.
Logarithms are natural and all exponents are real.

## Motivation

This provides the scalar concavity input for binary Rényi information
combining. It quantifies over every real order at least two, rather than
only integer orders or probabilities strictly inside the interval.

## Gap

The named-clause and literature boundary is the supplied preregistration.
No additional independent literature search is claimed. Other parameter
ranges and quantum conditional-entropy inequalities are outside this target.

## Route

Put $\psi(t)=h_\alpha((1-t)/2)$, $n=\alpha-1$ and
$r(t)=(1-t)/(1+t)$. For $0<r<1$, let

$$
T=\frac{1-r^n}{1+r^n},\quad
A=\frac{nr^{n-1}(1-r^2)}{1-r^{2n}},\quad
B=\frac{1-r}{1+r}T,\quad F=\frac{A-B}{1+B}.
$$

The certificate proves that $F$ is increasing. Its nonnegative derivative
uses $J_n(z)=(n-1)-(n+1)z+(n+1)z^n-(n-1)z^{n+1}\ge0$, obtained by two
applications of derivative-sign monotonicity on $[z,1]$ with $z>0$.
For $f=-\psi'>0$, differentiation gives $f'=fF(r(t))/t$.
Consequently $vf(vt)/f(t)$ increases in $t$ for $0<v<1$.
The inverse of $\psi$ decreases, so the first derivative of the transported
combining function decreases in its entropy input. Continuity gives
concavity on the closed interval. The cases $v=0$ and $v=1$ are respectively
a constant and the identity. No endpoint inverse derivative is required.

## Falsifier

A violation is a real $\alpha\ge2$, a permitted $y$, and two points and a
convex weight violating the stated concavity inequality. A source mismatch
or a prior settlement would affect the source or novelty claim independently
of kernel verification.


## Evidence

The settling declaration is `result : claim` in
`D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.lean`.
The companion `CachinElasticityMonotone.monotoneOn_F` supplies the real-power
certificate used on its live proof path. The inverse identities are proved
for the specified probability branch. Both declarations have axiom closure
contained in `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

This is a general real-parameter theorem with `utility: none`, using the
`open-problem-resolution` admission basis of #18704. The Scribe's Proved claim
covers exactly the alpha-at-least-two concavity clause. Other clauses of
Conjecture IV.18 remain outside this settlement.

## ASSUMED-UNVERIFIED

The paper locator and preregistration's literature boundary are supplied
source metadata. They have not been independently rechecked against later
literature in this implementation. The formal theorem has no mathematical
premise asserting the conjecture or its elasticity inequality.
