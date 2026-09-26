---
bibkey: kagey2026a400216tetrahelix
authors: Peter Kagey
year: 2026
title: OEIS A400216, A400217 and A400218, Boerdijk-Coxeter tetrahelix coordinates
doi: null
url: https://oeis.org/A400216
claim: "Three coordinate generating functions of one ordered Boerdijk-Coxeter tetrahelix are marked conjectured."
strata_touched:
  - D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions
license: citation-only
triage: anchor
---

# Boerdijk-Coxeter tetrahelix coordinate series

The related entries are https://oeis.org/A400216,
https://oeis.org/A400217 and https://oeis.org/A400218. Peter Kagey is credited
on September 21, 2026; the entries were created on September 23, 2026. Each
formula line labels its rational generating function conjectured.

The records give the first four vertices, in order, as (-1,-1,-1), (-1,1,1),
(1,-1,1), (1,1,-1), followed by (5/3,5/3,5/3), (31/9,1/9,1/9), and
(83/27,77/27,-13/27). They say 24 symmetries are possible and identify this
one by asymptotically maximizing x and then y. The formal construction uses
the displayed ordered vertices and face reflection. The asymptotic comparison
of all 24 choices is not part of the formal theorem.

Direct exact rational iteration gives the next three vertices as
(361/81,169/81,151/81), (1373/243,413/243,-163/243), and
(3895/729,3145/729,265/729), matching the rest of the OEIS ten-vertex
example. The exact match fixes the orientation used by the three entries.

The full OEIS JSON records were fetched on September 26, 2026. The full
15-page preprint https://arxiv.org/abs/1302.1174, associated with DOI
10.3390/math7101001, was read. Its Section 2 appends tetrahedra by face
reflection and then rotates them to obtain modified periodic helices;
Appendix A supplies reflection and rotation matrices. It does not state
the three scaled rational generating functions. The exact A-number search
in this repository, the pinned Mathlib theorem search, Loogle, and GitHub
repository search found no earlier formal settlement. These surfaces do
not establish exhaustive publication priority.
