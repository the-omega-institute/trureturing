---
bibkey: hamdar2025cubicawaycentral
authors: Mohammad H. Hamdar
year: 2026
title: "Hecke L-functions Away From The Central Line"
doi: null
url: https://arxiv.org/abs/2509.06152v2
claim: "For cubic Hecke L-functions over Q(sqrt(-3)), the first moment has a phase transition at Re(s)=1/3; at the transition, the principal cube term cancels the contribution from infinitely many dual cubic-Gauss residues, and at s=1/2 a Q^(5/6) secondary term is obtained."
strata_touched: []
license: citation-only
triage: anchor
---

# Cubic principal--dual residue cancellation

The source is [arXiv:2509.06152v2](https://arxiv.org/pdf/2509.06152v2),
updated 7 January 2026. This card records the exact cancellation mechanism
that is relevant to the project's joint-contour strategy. It is a literature
interface, not an independent proof audit or Lean certification.

## The proved model

For the squarefree cubic family over $\mathbb Q(\sqrt{-3})$, Theorem 1.2
gives, away from $s=1/3$,

$$
\sum_{\chi_q}L(s,\chi_q)w(N(q)/Q)
=C_s\widetilde w(1)Q
+E'_s\widetilde w(4/3-s)Q^{4/3-s}
+O(Q^{(11-6s)/10+\varepsilon}).
$$

At $s=1/3$ the two singular contributions meet and the theorem instead gives

$$
\sum_{\chi_q}L(1/3,\chi_q)w(N(q)/Q)
=C_{1/3}\widetilde w(1)Q\log Q+D_{1/3}Q
+O(Q^{9/10+\varepsilon}).
$$

The logarithmic transition comes from cancellation between the principal
sum's cube contribution and infinitely many residues of the dual Dirichlet
series of cubic Gauss sums. The terms are initially produced by different
parts of the approximate functional equation; the cancellation is established
only after the meromorphic residue formulas are matched.

At $s=1/2$, the same theorem gives a genuine secondary term

$$
E'_{1/2}\widetilde w(5/6)Q^{5/6}
$$

with an error $O(Q^{4/5+\varepsilon})$.

## Relation to the sixth-order Robin interface

This is the closest documented precedent for the project's proposed joint
contour above the sixth-power pole. It supports the methodological claim that
a principal pure-power term and a dual Gauss term must sometimes be combined
before estimating the contour. It does not supply the missing order-six
estimate, because the source explicitly relies on cubic Gauss-series residue
formulas from Kubota--Patterson and states that analogous formulas are not
known for orders $\ell\ge4$.

Therefore the transfer to the project's kernel
$\mathscr F_{j,a}(z)$ still requires a new order-six meromorphic identity,
including its moving quadratic twist, all convolution masks, and the signed
Robin restoration. The cubic result is a reusable template and a boundary
condition, not evidence that the sixth-order cancellation has already been
proved.

