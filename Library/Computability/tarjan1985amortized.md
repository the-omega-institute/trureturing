---
bibkey: tarjan1985amortized
authors: Robert Endre Tarjan
year: 1985
title: Amortized Computational Complexity
doi: 10.1137/0606031
url: https://doi.org/10.1137/0606031
claim: Amortized analysis accounts for the total cost of a sequence of operations rather than requiring the same worst-case cost at every operation.
strata_touched: []
license: citation-only
triage: anchor
---

# Cost paid by a decreasing potential

Tarjan's paper in *SIAM Journal on Algebraic Discrete Methods* 6(2),
306–318, is the standard amortized-analysis reference. The following
elementary telescoping version is supporting exposition; no particular
numbered theorem or physical cost model is attributed to the paper.

Let a uniform actual execution have macro states $s_j$, nonnegative
potential $\Phi_j$, and integer primitive costs $c_j\ge1$. Suppose each
nonterminal state supplies its next completed macro update, and for a
fixed input length $n$,

$$
\Phi_0\le q(n),\qquad
c_j\le p(n)(\Phi_j-\Phi_{j+1}),
$$

where $p(n)\ge1$ and $q(n)\ge0$. Then every finite prefix satisfies

$$
\sum_{j<m}c_j\le p(n)(\Phi_0-\Phi_m)\le p(n)q(n).
$$

An infinite sequence of nonterminal completed updates is impossible
because its first $m$ costs sum to at least $m$. A stuck or infinite
internal macro computation is separately excluded by the requirement
that the next completed update is supplied. Correctness of terminal
outputs and the cost of preparation and final readout are additional
obligations. When $p,q$ are polynomials and all these costs are included,
this is a polynomial primitive budget.

The potential may be an analysis tool unavailable to the running machine.
If its value is used to choose actions, computing it must also be paid
for. Merely defining a decreasing remaining-prefix length for SAT does
not give an inexpensive rule for choosing a still-completable prefix.
