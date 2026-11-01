---
bibkey: chvatal1975polytopes
authors: Vaclav Chvatal
year: 1975
title: On certain polytopes associated with graphs
doi: null
url: https://doi.org/10.1016/0095-8956(75)90041-6
claim: For a perfect graph the stable set polytope is described by nonnegativity and clique inequalities; finite paths give the bounded adjacent-sum description.
strata_touched:
  - D5/S1/Words/AdmissibleWords/PathStableSetPolytope
license: citation-only
triage: anchor
---

# Stable set polytopes of paths

## Verified locator

The bibliographic locator is https://doi.org/10.1016/0095-8956(75)90041-6.
Crossref identifies the article as V. Chvatal, On certain polytopes associated
with graphs, Journal of Combinatorial Theory, Series B 18 (1975), 138–154.
The public exposition at https://en.wikipedia.org/wiki/Perfect_graph states
that the convex hull of independent-set indicator vectors is given by the
nonnegative clique inequalities precisely for perfect graphs and cites this
article. The publisher page returned HTTP 403; the primary article's full
text was not inspected.

A path is bipartite and perfect. Its cliques have at most two vertices.
The singleton inequalities give coordinate upper bounds, including the
isolated vertex when the path has length one. The edge inequalities say
that adjacent occupancies sum to at most one.

The Lean proof uses an induction on the number of vertices. Given a mixture of tail
words, prepend either zero or the complement of the first tail bit. Both
operations preserve admissibility and extend affinely to tail means. Mixing
these two extensions with coefficient x0/(1-x1) restores the requested first
coordinate. When x1 is one, the first coordinate is zero. The one-coordinate
case is the interval between zero and one, and the empty case has a single
empty vector. This is a repository proof of a classical result, with no
third-party Lean code copied into the repository.
