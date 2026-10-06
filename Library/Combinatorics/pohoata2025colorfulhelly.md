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

## Omitting one indexed owner from each complete color

There is a different direct application which retains all but one
owner from each color. Let finite indexed congruence families
\(\{A_{ci}:i\in I_c\}\) each cover the same \(X\subseteq\mathbb Z\).
All positive moduli divide a fixed \(N>0\). Define the common locus

$$
Y=\{x\in X:\text{every color has exactly one indexed owner at }x\}.
$$

For an omission choice \(o(c)\), let
\(R(o)=\bigcup_c\bigcup_{i\ne o(c)}A_{ci}\). Then

$$
X\setminus R(o)=Y\cap\bigcap_c A_{c,o(c)}.
$$

Indeed, failure of all retained owners forces the omitted index to
be the unique owner in each complete color. Conversely, on Y any
point in every omitted owner belongs to no retained owner.
Consequently two different indexed owners in a color have disjoint
traces on Y. If their supports coincide, both traces are empty.

For the family of congruence traces on Y, the intersection-comatching
parameter is at most \(\omega(N)\). A common point and a witness
missing only the c-th selected trace show that its modulus does not
divide the lcm of all the others. Some prime coordinate therefore
has a strictly larger valuation at c than at every other selected
modulus. Different c require different prime divisors of N.

Theorem 1.3, applied to these traces rather than their complements,
thus supplies a successful omission from each of n colors whenever
\(n>\omega(N)\) and each color offers two distinct omission indices.
The exact displayed identity turns its empty intersection back into
coverage of the original X. This proves existence; the stronger
one-switch repair from any initial omission plan follows from the
direct divisor-lattice argument in
[Report864](../../docs/reports/erdos7-odd-covering/profile-notes/arithmetic/850-899/864-complete-color-covers-and-phase-product-obstruction.md#a-prime-coordinate-bound-allows-one-omission-from-every-color).

The common locus Y is not an individual owner's private region in
the original covering system. No product structure or prescribed
positive density of X is used. This application does not choose
ternary prefixes, free occupied parent labels, or cover the larger
hole created by subsequently deleting such parents.
