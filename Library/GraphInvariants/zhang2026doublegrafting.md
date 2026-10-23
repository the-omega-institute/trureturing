---
bibkey: zhang2026doublegrafting
authors: Wenlin Zhang
year: 2026
title: "From hypercubes to grids: sub-quorum colorings and structural bounds"
doi: null
url: https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex
claim: "The exact grafting theorem gives beta2(R(F))=4|V(F)|+beta2(F) and psi_sq(R(F))=5|V(F)| for every nonempty finite simple base graph."
strata_touched:
  - D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting
license: citation-only
triage: anchor
---

# Double-star grafting

## Verified locator

URL: https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex

The public working manuscript is dated 27 September 2026 and names Wenlin
Zhang. Its author footnote describes discussion with Rafik Sahbi and an
unsettled author list. This source is not the newer private joint journal
revision. The immutable TeX source has SHA256
`8e7531fc9de758aca4856b58311e221305ec408214bbba63827b02e336d64825`.

## Exact statement

Theorem `thm:grafting`, with the double-star and `thm:treegap` arguments,
uses centers u,v and leaves a,b adjacent to u and c,d adjacent to v.
For every nonempty finite simple graph F, attach one disjoint copy of
this six-vertex graph to each original vertex h by the edge ha. Preserve
all original edges. The resulting R(F) satisfies

- beta2(R(F)) = 4|V(F)| + beta2(F), where beta2 maximizes the size of an
  induced set of maximum degree at most one.
- psi_sq(R(F)) = 5|V(F)|, where a partial coloring counts its actual
  represented colors and requires a weak majority of its own color in
  each colored closed neighborhood. Uncolored vertices enter neither
  count.

The restriction/extension argument proves the first equality. For the
second, give the two centers one color, the four leaves distinct colors,
and leave the base uncolored. In the reverse direction, each restricted
gadget uses at most five colors. Every base-exclusive color can be
represented by a distinct base vertex; its gadget then has at most four
colors. A stronger local formulation bounds the colors in each base
vertex together with its own gadget by five, and the union bound gives
the same global estimate with arbitrary original base edges.

These are source-attested results. No claim of literature priority or
originality beyond this public source is made.
