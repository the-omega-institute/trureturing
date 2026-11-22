---
bibkey: ehrenborgsteingrimsson2000excedance
authors: Richard Ehrenborg; Einar Steingrímsson
year: 2000
title: The Excedance Set of a Permutation
doi: 10.1006/aama.1999.0671
url: https://doi.org/10.1006/aama.1999.0671
claim: "Proposition 2.1 gives [vbaw] = [vabw] + [vbw] + [vaw]. Lemma 2.3 gives [aw] = [wb] = [w]."
strata_touched:
  - D5/S3/Combinatorics/Permutation/AdjacentExcedanceSet
  - D5/S3/Combinatorics/Permutation/KurkovA329369ConjectureFour
license: citation-only
triage: anchor
---

# The Excedance Set of a Permutation

Richard Ehrenborg and Einar Steingrímsson, *Advances in Applied Mathematics* 24,
284–299 (2000). Proposition 2.1 on pages 286–287 counts permutations with a prescribed strict
excedance set by separating the two deletion cases from the swap case. Lemma
2.3 on page 287 proves that a leading nonexcedance or trailing excedance can
be removed. [Author copy](https://www.ms.uky.edu/~jrge/Papers/excedance.pdf).

The Lean counts use permutations of a finite ordinal with positions numbered
from zero. In the bracket notation, a word of length $d$ specifies the first
$d$ positions of a permutation of size $d+1$. The last position is always a
nonexcedance. This gives the correspondence between the word identities and
the strict-excedance sets used in the formalization.

## Verified locator

DOI `10.1006/aama.1999.0671`, https://doi.org/10.1006/aama.1999.0671.
Ehrenborg and Steingrímsson give all three case bijections in Proposition 2.1
(pp. 286–287), using two deletions and one adjacent swap. In Lemma 2.3 (p. 287)
they prove the boundary deletion identities $[aw] = [wb] = [w]$ by deleting a
trailing excedance and using duality for the leading nonexcedance.
