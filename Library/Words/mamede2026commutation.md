---
bibkey: mamede2026commutation
authors: Ricardo Mamede, Jose Luis Santos, Diogo Soares
year: 2026
title: Maximum number of one-element commutation classes of a permutation
doi: 10.48550/arXiv.2601.09395
claim: Lemmas 2.4 and 3.1 give exterior support and extremal orientation; Lemmas 3.2 and 3.4 give uniqueness at an extremal endpoint; Lemma 3.6 gives a source-word shape, Proposition 3.7 separates factors when j<i, and Proposition 3.8 gives deletion injectivity.
strata_touched:
  - D5/S1/Words/Permutations/MamedeAdjacentWords
  - D5/S1/Words/Permutations/MamedeSourceAction
  - D5/S1/Words/Permutations/MamedeConditionalConverse
  - D5/S1/Words/Permutations/MamedeShapeExtraction
  - D5/S1/Words/Permutations/MamedeDeletionEquiv
  - D5/S1/Words/Permutations/MamedeExtremalOrientation
  - D5/S1/Words/Permutations/MamedeEndpointUniqueness
  - D5/S1/Words/Permutations/MamedeFactorSeparation
  - D5/S1/Words/Permutations/MamedeOrderFreeFiber
license: citation-only
triage: anchor
---

# Maximum number of one-element commutation classes of a permutation

## Verified locator

DOI [10.48550/arXiv.2601.09395](https://doi.org/10.48550/arXiv.2601.09395)
identifies [arXiv:2601.09395v1](https://arxiv.org/html/2601.09395v1).
The cited scope is Definition 3.1, Lemmas 2.4, 3.1, 3.2 and 3.4, Lemma 3.6 (first
orientation), and Propositions 3.7 and 3.8. The conditional converse below is a new formal claim, not a
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

## Extremal orientation

Lemma 3.1 and the exterior support observation of Lemma 2.4 also support
`MamedeExtremalOrientation.extremal_orientation`. Its inputs are only a
nonempty reduced consecutive word. It chooses the attained minimum and maximum
generator indices, proves exterior fixedness, and derives either an endpoint
map from the minimum position to the position above the maximum, with a full
descending run, or the opposite endpoint map with a full ascending run.
The proof uses reversed words to represent inverse permutations. This is a
formalization of a published intermediate result, not a new resolution.

The nonoscillating source-admissibility implication still requires strict
internal endpoint extraction, the other endpoint equations, nonoscillation
under reversal, and a proof that arbitrary sources enter the conditional
`j<i` fiber theorem below. The extremal theorem does not assume or
establish `i<=j`, and does not settle Conjecture 5.1.

## Extremal endpoint uniqueness

`MamedeEndpointUniqueness.extremal_endpoint_unique` compares two reduced
consecutive words with equal permutation products. If their first letters
are the same common minimum or maximum, the words are equal; the same holds
for their last letters. The theorem assumes the generator bounds for both
words and compares endpoints on the same side. It does not assume an
oscillation or compare a first endpoint with a last endpoint.

This is a formalization of the combined endpoint statement in Lemmas 3.2
and 3.4. Lemma 3.2 identifies reduced consecutive words with an extremal
endpoint as oscillations, and Lemma 3.4 gives uniqueness at each such
endpoint. Omitting the oscillation premise does not claim new published
mathematics. The proof alternates forced initial descents with reflected
ascents, using induction on word length; reversal supplies the right
endpoint cases.

## Separated source factors

`MamedeFactorSeparation.source_shape_unique_of_j_lt_i` formalizes the
factor-separation part of Proposition 3.7's proof. For
`1<=m<j<i<M<=n`, two reduced consecutive words with equal products and
first-orientation `sourceShape m M i j` decompositions are equal. Each
prefix has generators in `(m,j)` and each suffix in `(i,M)`. Both shapes
are actual hypotheses; no nonoscillation or endpoint equations are assumed.

The prefix and suffix products fix every position outside `[m+1,j]` and
`[i+1,M]`, respectively. The central excursion fixes both intervals. To
prove this, split `descending(i-1,m)` before `j` and use the existing
three-cycle action formula for `deletedExcursion`. The extra descending
run has length `i-j-1` and is empty when `i=j+1`; the definition of
`descending` with reversed bounds would not describe that empty case.
Commute the central product past the suffixes and cancel it. Evaluation
on the prefix interval recovers the equal prefix products, and left
cancellation recovers the equal suffix products. Each subword is reduced
and consecutive. Chain boundaries give the common maximal last letter
`j-1` of nonempty prefixes and the common minimal first letter `i+1` of
nonempty suffixes. The endpoint theorem identifies them. Minimality
against the empty representative covers empty factors.

The order-free guarded-walk argument in
`MamedeOrderFreeFiber.singleton_fiber_unique_of_j_lt_i` supplies the missing
shape extraction for every `singletonWord n sigma a` under
`1<=m<j<i<M<=n`, the three endpoint equations
`sigma(M+1)=m`, `sigma(m)=j+1`, `sigma(i)=M+1`, and exterior fixedness
outside `[m,M+1]`. It forces the descending `j..m`, ascending `m..M`,
and descending `M..i` runs independently of the order between `i` and
`j`. Alignment at the shared `m` and `M` markers yields
`sourceShape m M i j a p q`, including its exact prefix bounds
`m<k<j` and suffix bounds `i<k<M`. Applying the factor-separation
theorem to any two such singleton words gives equality. The proof includes
`i=j+1` and empty prefix or suffix. The finite word
`[2,1,2,3,4,3]` at `n=4` witnesses nonvacuity; it is not used to
establish the universal extraction.

This is the conditional first-orientation fiber argument of published
Proposition 3.7. The older frozen `endpointExteriorFixedSource` and
its extraction theorems still require `i<=j`; the new argument uses
independent interior bounds. Deriving the strict internal endpoints and
the endpoint equations from an arbitrary nonoscillating source remains
unproved, as do the other branches of Conjecture 5.1. The identification
of the paper's commutation classes with `singletonWord` remains a
source-translation judgment. KPI is 0.
