---
bibkey: annor2025domination
authors: Dickson Y. B. Annor
year: 2025
title: Domination Parameters of Graph Covers
doi: 10.48550/arXiv.2502.14341
claim: "Conjecture 14 asserts a universal c > 0 with gamma(G) >= c*k*gamma(F) for every k-fold graph cover G of F."
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/AnnorCoverRefutation
license: citation-only
triage: anchor
---

# Source assertion and bounded search

Original checked: https://arxiv.org/html/2502.14341v2 (2025-11-25),
Introduction and Conjecture 14. The exact assertion is:

> There exists a constant c>0 such that for every k-fold cover G of a graph F
> we have gamma(G)>=c*k*gamma(F).

Mathematical typography is transcribed into ASCII. The following sentence
suggests c=3/5; refuting that value alone does not refute Conjecture 14.
Graphs are finite, undirected and simple. A covering projection is onto
and restricts to a bijection on each open neighborhood. The source explains
constant fold for connected bases. It does not require the cover graph to
be connected. Domination means every vertex outside the set has a neighbor
in the set; its number is the minimum size of such a set.

This source attests the conjecture, not the repository's refutation.
The proof in AnnorCoverRefutation constructs connected bases, positive
folds and strict violations for every positive real c. Its literature
status is suspected novel after a bounded check, not globally certified.

Search on 2026-09-07 Asia/Singapore (2026-09-06 UTC):

- OpenAlex work W4407806657 and its direct citing-work query recorded zero
  citations. This is incomplete indexing evidence, not a novelty proof.
- arXiv query `all:"Annor" AND all:domination` returned the source and
  arXiv:2506.03646v3. The full latter HTML, dated 2026-06-05, was read:
  it treats relations among three domination parameters and contains no
  graph-cover theorem or refutation.
- arXiv searches for perfect codes and graph covers, and OpenAlex searches
  for `"regular graphs" "perfect codes" "covers"`, were inspected.
  They recover older perfect-code literature; no inspected result is
  claimed as a new ingredient. Full citation-forward coverage is absent.
- Direct products of complete graphs have established domination theory:
  see the separate note `vemuri2019domination`. The elementary lower bound
  used here is not claimed new.
- Neumann's exposition of the common finite covering theorem was read,
  including the Angluin-Gardiner regular case. Combining that classical
  result with K_(d+1) already yields covers with perfect codes; see
  `neumann2009on`. No novelty is claimed for this existence mechanism.
- The 1975 perfect-code survey retrieval returned HTML, not a PDF, and
  was not counted as full-text evidence. Broad coding-theory hits do not
  substitute for a complete citation-forward search.

The stored search responses and preregistrations are in the implementation
attempt log referenced by the worker result. Independent mathematical and
novelty review remains required before merging or counting a solved problem.

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2502.14341. Independently resolved and
checked on 2026-09-07 Asia/Singapore against
https://arxiv.org/html/2502.14341v2 (2025-11-25), Introduction and
Conjecture 14. These locate the finite simple graph-cover conventions and
the universal positive-constant conjecture quoted above. The source
attests that conjecture, not the repository's refutation or its novelty.
