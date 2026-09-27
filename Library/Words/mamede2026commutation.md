---
bibkey: mamede2026commutation
authors: Ricardo Mamede, Jose Luis Santos, Diogo Soares
year: 2026
title: Maximum number of one-element commutation classes of a permutation
doi: 10.48550/arXiv.2601.09395
claim: Lemma 3.6 gives a first-orientation source-word shape, and Proposition 3.8 constructs an injection by deleting part of its excursion.
strata_touched:
  - D5/S1/Words/Permutations/MamedeAdjacentWords
  - D5/S1/Words/Permutations/MamedeSourceAction
  - D5/S1/Words/Permutations/MamedeConditionalConverse
license: citation-only
triage: anchor
---

# Maximum number of one-element commutation classes of a permutation

## Verified locator

DOI [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395)
identifies [arXiv:2601.09395v1](https://arxiv.org/html/2601.09395v1).
The cited scope is Definition 3.1, Lemma 3.6 (first orientation), and
Proposition 3.8. The conditional converse below is a new formal claim, not a
result asserted by those source passages.

[Mamede, Santos and Soares, arXiv:2601.09395v1](https://arxiv.org/html/2601.09395v1)
study reduced adjacent-transposition words whose consecutive letters differ by
one. In the first orientation of Lemma 3.6, the relevant non-oscillating source
word has the form `p ++ descending(j,m) ++ ascending(m+1,M) ++
descending(M-1,i) ++ q`, with prefix letters strictly between `m` and `j` and
suffix letters strictly between `i` and `M`. Proposition 3.8 deletes a part of
that excursion and proves the resulting map injective. It does not assert the
conditional surjectivity proved in the associated Lean modules.

The conditional result requires one **actual singleton reduced source word** with that
first-orientation shape. It proves that every singleton reduced word of the
target permutation factors around `descending(j,i)` with the same support
bounds and lifts to a strictly longer singleton reduced source word. The
source-shape premise is not derived from the other permutation hypotheses in
the Lean development. No reflected orientation, cardinality equality,
oscillation branch, induction, Conjecture 5.1, or KPI conclusion follows from
this conditional statement.

The nonfixed endpoint clauses and nonoscillating singleton existential in
`exactSourceHypotheses` retain the paper's context, but the two conditional
proofs do not use them once the actual shaped singleton is supplied. The
existential does not establish `sourceShape` for that singleton.
