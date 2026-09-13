---
bibkey: chervov2025cayleypy
authors: A. Chervov and others
year: 2025
title: 'CayleyPy Growth: Efficient growth computations and hundreds of new conjectures on Cayley graphs'
doi: 10.48550/arXiv.2509.19162
claim: Conjecture 2 asserts eventual quasipolynomial word distance for every polynomial-time constructible generator family; it is false as stated.
strata_touched:
  - D5/S0/CayleyGrowth/QuasipolynomialWordMetricRefutation
license: citation-only
triage: anchor
---

# CayleyPy Growth

The third CayleyPy paper reports about two hundred computational conjectures on
Cayley and Schreier graphs of symmetric groups, most of them about diameters and
growth. Two of them are quantified over every generator family that an algorithm
can write down in polynomial time.

Conjecture 1, labelled "extremely optimistic" by the authors, states that for any
such family of generators of `S_n` the diameter of the Cayley graph is given by a
quadratic or linear quasipolynomial in `n`, at least for `n` large enough.
Conjecture 2, labelled the same way, states the corresponding assertion for the
distance from the identity to a marked element `g_n` supplied together with the
generators.

Conjecture 2 is false as written, and the repository declaration refutes it. The
generators are all transpositions of `Fin n`, which one algorithm writes down in
time quadratic in `n`; the marked element is a fixed transposition exactly when
`n` is a perfect square and the identity otherwise, which a square test decides.
The distance is then the indicator of the squares, and the repository proves that
no function eventually equal to that indicator is eventually quasipolynomial, of
any degree rather than only of degree at most two. The polynomial-time hypothesis
is discharged outside Lean; the two objects are given by closed formulas, so no
complexity model is needed to see that they are constructible.

The authors anticipate a defect of this kind without exhibiting one. Their
discussion reads: "Taking into account the amount of examples confirming the
conjecture, it is natural to believe that it is true in one or another way. It
might be that one needs to restrict the class of generators." The refutation turns
that remark into a theorem: some restriction is necessary, not merely plausible.
It says nothing about any restricted form of the conjecture, and nothing about
Conjecture 1, whose refutation would need a diameter formula for two generator
families rather than a single distance.

## Search log

- 2026-09-13: Read arXiv:2509.19162v2 in full. Conjectures 1 and 2 appear in
  Section 3.2 with the quantifiers quoted above; the condition of Conjecture 2
  appears in no theorem of the paper.
- 2026-09-13: Searched the pinned Mathlib checkout for quasipolynomial growth and
  for word metrics of Cayley graphs. `Mathlib/Combinatorics/SimpleGraph/Cayley.lean`
  supplies `mulCayley` and its adjacency characterisation and is used directly; no
  notion of quasipolynomiality exists there, so the predicate is defined here.
- 2026-09-13: Searched the repository for Cayley-graph and word-metric statements.
  `D5/S3/ContinuousObservables/AsymmetricPermutationDistances` measures observer
  distance along permutation orbits and does not bear on the word metric.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2509.19162
