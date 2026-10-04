---
bibkey: pohoata2025colorfulhelly
authors: "Cosmin Pohoata; Kevin Yang; Shengtong Zhang"
year: 2025
title: "Colorful Helly via induced matchings"
doi: 10.48550/arXiv.2501.17149
url: https://arxiv.org/abs/2501.17149v2
claim: "The colorful Helly number of any set family is at most one plus its comatching-with-intersection number."
strata_touched: []
license: citation-only
triage: anchor
---

# Whole colorful subcovers from private incidences

The primary text is arXiv:2501.17149v2, deposited 29 January 2025.
Theorem 1.3 states

$$
\eta(X,\mathscr F)\le 1+\tau'(X,\mathscr F).
$$

Here the colorful Helly number uses finite subfamilies: if each
of the indicated color families has empty intersection, one can
select one set of each color whose joint intersection is empty.
The parameter $\tau'$ is the largest r admitting sets
$F_1,\ldots,F_r$ and points $x_1,\ldots,x_r,x_0$ such that
$x_s\in F_t$ exactly when $s\ne t$, and $x_0$ belongs to every
$F_t$. The extra common point is part of the hypothesis.

For a family of supports $S_i\subseteq X$, apply the theorem to
their complements in the same X. Its parameter becomes the largest
r admitting selected supports and points with

$$
x_s\in S_{i_t}\iff s=t\quad(1\le s,t\le r),
\qquad
x_0\notin\bigcup_{t=1}^r S_{i_t}.
$$

Thus, for nonempty X and n positive, given n finite color families
each covering all of X, a bound
$\tau'\le n-1$ supplies a whole subcover choosing one support per
color. If fewer than n colors are needed, extend that selection by
arbitrary supports from the remaining nonempty color families.
This is a direct complement application of the cited theorem.

In the masked-component interface for odd covering systems, X can
be the same component source together with all higher q-digit
suffixes after removing the first digit. The support retains every
literal cofactor, ternary and suffix condition of its original.
Each first-digit color must cover that entire common X. A private
point for each selected support and one point missed by all selected
supports measure a different incidence pattern from pairwise
prime-phase collisions among top originals.

No bound $\tau'\le82$ is established for the actual 83-color source.
The theorem also supplies no ternary prefix assignment, freshness
of numerical replacement moduli, or count and modulus-sum payment.
Those are additional arithmetic obligations. No source text is
vendored and no Lean verification is asserted by this note.
