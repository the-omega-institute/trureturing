---
bibkey: laurent1994seriesparallel
authors: Monique Laurent
year: 1994
title: The real positive semidefinite completion problem for series-parallel graphs
doi: 10.1016/0024-3795(95)00741-5
url: https://ir.cwi.nl/pub/5067/5067D.pdf
claim: Closed odd-subset angle inequalities characterize real correlation completion on series-parallel graphs; a same-vertex chordal supergraph with cliques of size at most three additionally supplies rank at most three by chordal assembly.
strata_touched: []
license: citation-only
triage: anchor
---

# Simultaneous angle extension and partial two-tree completion

The CWI report BS-R9439 gives the projected metric-polytope inequalities
on printed page 4, equation (2.2). Printed page 7, Theorem 4.2 and
Proposition 4.3, relates cycle correlation matrices to normalized angle data.
Printed page 10, Theorem 4.7, characterizes equality between the elliptope
and the cosine image of the metric polytope for graphs without a K4 minor.
The journal version appeared in Linear Algebra and its Applications in 1997.

The formal statement uses the supplied existence of a chordal supergraph
on the same vertex set, with every clique of cardinality at most three.
It does not substitute a graph-minor characterization for that hypothesis.
Its real rank-three bound is obtained separately by the existing
rank-bounded chordal completion theorem. The feasibility statement alone
is not cited as a rank-three theorem.

For simultaneous fill values, give an edge of angle theta cost theta when
its endpoint signs agree and cost pi minus theta when they differ.
The original simple-cycle inequalities imply that every closed walk with
opposite endpoint signs costs at least pi. Repeated vertices are removed
or isolate a shorter odd signed loop. For a missing edge, take the supremum
of zero and pi minus every odd signed path cost between its endpoints.
Joining an even path to an odd path proves compatibility with every upper
bound. The four signed endpoint states carry a common boundary distance;
its triangle inequalities preserve all closed-walk bounds after insertion.
Maximality on the finite set of graphs constructs a single angle table.
Closed endpoints and disconnected graphs require no separate strictness
or connectivity assumption.

The existing three-cycle criterion turns the angle conditions on each
clique into a PSD block. A three-slot enumeration permits repeated vertices
and therefore also handles cliques of cardinality one or two. Empty cliques
are handled by the empty matrix. Existing chordal assembly then constructs
the global PSD completion in rank at most three. The result is classical;
no mathematical novelty or external open-problem resolution is claimed.
No source text or code is copied from the cited publications.

## Verified locator

- CWI report, equation (2.2), Theorem 4.2, Proposition 4.3 and Theorem 4.7: https://ir.cwi.nl/pub/5067/5067D.pdf
- CWI bibliographic record: https://ir.cwi.nl/pub/5067
- Journal DOI: https://doi.org/10.1016/0024-3795(95)00741-5
- Cycle criterion and uniform cycle rank bound: https://arxiv.org/abs/1203.6602v2
- Rank-bounded chordal assembly context: https://arxiv.org/abs/1204.0734v1
