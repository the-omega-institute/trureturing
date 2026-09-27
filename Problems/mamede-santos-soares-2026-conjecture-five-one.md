---
slug: mamede-santos-soares-2026-conjecture-five-one
bibkey: mamede2026commutation
doi: 10.48550/arXiv.2601.09395
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/MamedeShapeExtraction
  - D5/S1/Words/Permutations/MamedeConditionalConverse
  - D5/S1/Words/Permutations/MamedeOrderFreeFiber
---

# Mamede--Santos--Soares Conjecture 5.1

## Problem

Conjecture 5.1 states: for every $n\geq1$ and every permutation
$\sigma\in S_{n+1}$, $|R_\bullet(\sigma)|\in\{0,1,2,4\}$.
Here $R_\bullet(\sigma)$ is the set of one-element commutation classes of
reduced adjacent-transposition words. The paper's Theorem 3.9 proves the
upper bound four; the remaining assertion excludes exactly three classes.
The paper identifies these classes with reduced words whose successive
generator indices differ by one, as in the repository's `singletonWord`.
The source is [Section 5 of arXiv:2601.09395v1](https://arxiv.org/html/2601.09395v1#S5).

## Motivation

`MamedeDeletionEquiv.source_deletion_equiv` gives a first-orientation
equivalence of actual singleton-word fibers under `exactSourceHypotheses`.
Its forward map deletes part of the forced excursion and reduces length by
the positive, fixed length of `deletedExcursion`. The existing
`source_shape_for_every_singleton` and `source_deletion_surjective` provide
the all-source shape and onto directions. This is a conditional count-preserving
step, not a verified resolution of Conjecture 5.1. KPI: 0.

`MamedeExtremalOrientation.extremal_orientation` derives attained generator
extrema, exterior fixedness, an endpoint orientation, and a full extremal run
from any nonempty reduced consecutive word. It supplies the extremal part of
the source adapter. Strict internal endpoints and the remaining source
adapter obligations are still unproved; the conditional `j<i` fiber step
is proved below. This intermediate result does not change KPI.

`MamedeEndpointUniqueness.extremal_endpoint_unique` proves that two reduced
consecutive words with the same product and the same first (or the same
last) letter are equal when that letter is a minimum of both words or a
maximum of both words. This formalizes the endpoint uniqueness ingredient
of Lemmas 3.2 and 3.4. Together with the endpoint assumptions in the
conditional fiber theorem below, it helps identify all words in a `j<i`
fiber. It does not change KPI.

`MamedeFactorSeparation.source_shape_unique_of_j_lt_i` supplies the
factor-separation step of Proposition 3.7: under `1<=m<j<i<M<=n`, equal-product
reduced consecutive words with the two actual first-orientation source shapes
are equal. It recovers the separate prefix and suffix products and checks
all endpoint-uniqueness premises, including empty factors and `i=j+1`.
The companion `MamedeOrderFreeFiber.singleton_fiber_unique_of_j_lt_i`
extracts those shapes for every singleton word from the three endpoint
equations and exterior fixedness under `1<=m<j<i<M<=n`, then applies
factor separation to prove whole-fiber uniqueness. Its local extraction
gives the exact `m<k<j` prefix and `i<k<M` suffix bounds. The
quantified proof covers `i=j+1` and empty outer factors. This settles
the conditional first-orientation fiber step of Proposition 3.7 in
the repository's adjacent-word model. The older frozen extraction
theorems retain their `i<=j` telescope. KPI remains 0.

## Gap

The reflected orientation, oscillating and involutive branches, and a global
count argument for every permutation remain unproved. The induction also needs
to derive the exact endpoint and exterior hypotheses from an arbitrary
nonoscillating source, up to permutation inversion, and handle the terminating cases.
The class-to-word correspondence and the paper's upper bound still require
formal justification in this adjacent-word model before the full conjecture
can be claimed. Research target: [#10285](https://github.com/the-omega-institute/trureturing/issues/10285).

## Route

Establish the reflected deletion branch and the oscillating and involutive
cases. Then derive the endpoint and exterior conditions from arbitrary
nonoscillating sources, justify the class-to-word correspondence and upper
bound in the formal model, and close the global induction.

## Falsifier

A permutation with exactly three one-element commutation classes would refute
the conjecture. For the partial deletion result, a source satisfying
`exactSourceHypotheses` whose singleton-word fibers fail the stated
length-dropping equivalence would refute the formal statement.

## Evidence

The source statement is Conjecture 5.1 in Section 5 of
arXiv:2601.09395v1. `D5/S1/Words/Permutations/MamedeDeletionEquiv.lean`
proves the conditional first-orientation equivalence using the frozen shape
and lifting results. `Library/Words/mamede2026commutation.md` separates the
paper's deletion injection from the repository-derived converse.

## Triage

`theorem`. The current Lean result handles one conditional first-orientation
branch. The global conjecture remains open.

## ASSUMED-UNVERIFIED

The identification of the paper's commutation classes with the repository's
`singletonWord` predicate is a source-translation judgment, not a Lean
theorem. No formal proof of the reflected, oscillating, involutive, or global
count cases is claimed here.
