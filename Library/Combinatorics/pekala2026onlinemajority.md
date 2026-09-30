---
bibkey: pekala2026onlinemajority
authors: Paweł Pękała
year: 2026
title: "On-line majority edge-colourings of graphs"
doi: null
url: https://arxiv.org/abs/2609.37973
claim: "Problem 11 asks whether, for n in {5,6,7}, Algorithm has an online majority edge-colouring strategy using at most four colours against every Presenter strategy when the final graph has n vertices and minimum degree exactly 2."
strata_touched:
  - D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation
license: citation-only
triage: anchor
---

# Online majority edge-colouring at small order

Section 6, Problem 11 of arXiv:2609.37973v1 asks the question in the
front-matter claim. Presenter reveals edges of a simple graph one by one;
Algorithm colours each edge immediately. A majority edge-colouring has no
colour on more than half the edges incident with any vertex. The final
minimum degree is **equal to** two. The source proves a Presenter win for
`n >= 8` (Observation 10) and notes that one greedy four-colour strategy
fails already at `n = 5`; neither statement resolves Problem 11.

The source was checked at the arXiv HTML version on 2026-09-30. Issue
#11457 records the statement and the bounded prior-work search made before
the finite-game probe. That search does not establish global priority.

## Verified locator

- URL: https://arxiv.org/html/2609.37973 (v1, submitted 2026-09-29;
  Section 6, Problem 11, retrieved 2026-09-30).
