---
bibkey: boyerkuenzellylepellico2025wellhued
authors: Geoffrey Boyer, Kirsti Kuenzel, Jeremy Lyle, Ryan Pellico
year: 2025
title: "Well-hued graphs with first difference two"
doi: 10.48550/arXiv.2506.04993
url: https://arxiv.org/abs/2506.04993v1
claim: "Section 3, Conjecture 2 proposes the unrestricted balanced multipartite characterization with independence number alpha(G)."
strata_touched:
  - D5/S3/Combinatorics/Graph/Products/BoyerKuenzelLylePellicoConjectureTwoRefutation
license: citation-only
triage: anchor
---

# The unrestricted well-hued graph conjecture

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2506.04993

Version 1: https://arxiv.org/abs/2506.04993v1

Section 3, Conjecture 2, printed page 10, is the target. The introduction
defines maximal colorability using induced subgraphs and inclusion-maximal
vertex sets, with recoloring allowed. Well-huedness concerns every positive
number of colors.

The conjecture equates connected well-huedness, sequence
`(alpha(G), 2 alpha(G), ..., k alpha(G))`, and chromatic number `k` with
being a spanning subgraph of the balanced complete `k`-partite graph whose
parts have size `alpha(G)`, subject to an induced edgeless-graph exclusion
outside every closed neighborhood. The overline on the forbidden
`K_alpha(G)` is essential: it means an independent set of that order.

Theorem 4 treats independence number two. The paragraph introducing
Conjecture 2 explicitly replaces two by `alpha(G)`; the following paragraph
returns to independence number two. The general conjecture is therefore
distinct from that restricted theorem.

The Lean result refutes the general conjecture using the three by three
rook graph. The known rook-graph classification and maximal-colorability
obstruction belong to Goddard, Kuenzel and Melville (2022), cited in the
companion Library note. No new classification or repaired conjecture is
asserted.

The arXiv version page identifies the article license as CC BY-NC-SA 4.0
(https://creativecommons.org/licenses/by-nc-sa/4.0/). This note is an original
summary for citation; no source code or proof text is copied.
