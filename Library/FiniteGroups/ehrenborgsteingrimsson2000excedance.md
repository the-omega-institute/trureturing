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
284–299 (2000). Proposition 2.1 counts permutations with a prescribed strict
excedance set by separating the two deletion cases from the swap case. Lemma
2.3 proves that a leading nonexcedance or trailing excedance can be removed.

The Lean counts use permutations of a finite ordinal with positions numbered
from zero. In the bracket notation, a word of length $d$ specifies the first
$d$ positions of a permutation of size $d+1$. The last position is always a
nonexcedance. This gives the correspondence between the word identities and
the strict-excedance sets used in the formalization.
