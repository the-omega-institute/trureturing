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
  - D5/S1/Words/Permutations/MamedeShapeExtraction
  - D5/S1/Words/Permutations/MamedeDeletionEquiv
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
source-shape premise is derived for every singleton source word by the separate
`source_shape_for_every_singleton` theorem under `endpointExteriorFixedSource`,
which omits the nonoscillating existential and separate nonfixed clauses of
`exactSourceHypotheses`.
No reflected orientation, cardinality equality,
oscillation branch, induction, Conjecture 5.1, or KPI conclusion follows from
this conditional statement.

The nonfixed endpoint clauses and nonoscillating singleton existential in
`exactSourceHypotheses` retain the paper's context, but the two conditional
proofs do not use them once the actual shaped singleton is supplied. The
existential alone does not assert `sourceShape`; the separate Lean theorem
establishes it using the endpoint equations, exterior fixed points, and an
actual reduced consecutive source word.

The new `source_forced_runs` theorem applies to **each** singleton reduced
source word under `endpointExteriorFixedSource`. Its three separate factorizations
force a descent from `j` to `m`, an ascent from `m` to `M`, and a descent from
`M` to `i`, with one-sided prefix/suffix bounds. Every generator lies in
`[m,M]`. The theorem follows the endpoint strands and the repository's
rightmost-first permutation action. The new
`source_shape_for_every_singleton` theorem aligns the shared occurrences of
`m` and `M`, producing one `fullExcursion` and both strict `sourceShape`
support bounds. The endpoint-based strengthening omits the nonoscillating
singleton existential and separate nonfixed endpoint clauses required by
`exactSourceHypotheses`; it is a repository-derived Lean result, not a result
attributed to the cited paper. The paper derives endpoint identities from a
chosen nonoscillating word, whereas the endpoint-only Lean shape theorem
assumes those identities directly: `exactSourceHypotheses` implies
`endpointExteriorFixedSource` by projection, while the endpoint-only predicate
omits nonoscillation and the explicit nonfixed endpoint clauses. The
paper-to-Lean translation remains subject to independent source review.
Conjecture 5.1 remains open; KPI is 0.

The repository-derived `source_deletion_equiv` combines the all-source shape
result with a new forward deletion proof and the conditional lifting result.
It identifies the actual singleton-word fibers of `sigma` and
`sigma * gamma⁻¹` under `exactSourceHypotheses`, where `gamma` is the product
of `deletedExcursion`. For every shaped source, the forward word is
`imageWord`, and its length drops by the positive, fixed length of
`deletedExcursion`. The forward proof establishes consecutiveness and
reducedness; the first `j` in the word recovers the prefix, including when
the suffix contains `j`. The forward deletion/injection is supported by
Proposition 3.8 of the paper; the conditional converse and resulting
equivalence are repository-derived.
This result does not settle the reflected orientation, oscillation and
involution cases, or the global count in Conjecture 5.1.
