---
bibkey: standard2026pathpyramid
authors: Wikipedia contributors
year: 2026
title: Perfect graph — polyhedral characterization
doi: null
url: https://en.wikipedia.org/wiki/Perfect_graph
claim: The convex hull of independent-set indicator vectors on the three-vertex path is the pyramid over the unit square with the middle-vertex indicator as apex.
strata_touched:
  - D5/S1/Words/AdmissibleWords/PathStableSetPolytope
license: citation-only
triage: anchor
---

# The three-vertex stable-set pyramid

## Verified locator

The exact upstream locator is:
https://en.wikipedia.org/wiki/Perfect_graph

The retrieved polyhedral-characterization passage identifies the polytope
as the convex hull of independent-set indicator vectors. Only this standard
construction is needed for the direct three-vertex calculation below.
The existing `D5/L/Words/chvatal1975polytopes` note supplies the separately
cited general path characterization; its Citation is unchanged.

## Shared source chain and declaration bridge

The stable-set convex hull is the standard construction; the local
`vertices` are its indicator vectors because admissible binary words have
no adjacent ones. On the path with vertices 0,1,2, these vectors are
`(0,0,0), (1,0,0), (0,0,1), (1,0,1), (0,1,0)`.

For `convexHull_three_pyramid`, the first four indicators have convex hull
`{(u,0,v) : u,v in [0,1]}`, the unit-square base, and the fifth is the apex.
Taking the hull of the base and apex gives
`x=(1-t)(u,0,v)+t(0,1,0)` with t,u,v in [0,1]. This immediately implies
nonnegativity and `x0+x1<=1`, `x1+x2<=1`.
Conversely, those inequalities imply `t=x1 in [0,1]`. If t<1, take
`u=x0/(1-t)` and `v=x2/(1-t)`; the inequalities put both in [0,1].
If t=1, they force x0=x2=0, giving the apex. Thus both the inequality
description and the full parametrization in the Lean conjunction follow.
The local proof starts from `convexHull_vertices 3`, removes redundant
coordinate upper bounds, and uses precisely this two-case parametrization.
This is a direct consequence of the standard hull construction, not an
attribution of a separately named pyramid theorem to the exposition.

## What this note does and does not attest

Attested by this repository's own retrieval: the exposition's indicator-hull
description. The local declaration and its two-case construction were read;
the five indicators and the algebraic bridge are explicit above.

The round-19 classification is received from issue #6298. Chvatal's 1975
primary text was not retrieved or checked in this implementation;
attribution of the exact pyramid statement to that paper remains
`ASSUMED-UNVERIFIED`. No earliest-source claim is made.
