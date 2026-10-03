---
slug: mamede-santos-soares-2026-conjecture-five-one
bibkey: mamede2026commutation
doi: 10.48550/arXiv.2601.09395
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/MamedeShapeExtraction
  - D5/S1/Words/Permutations/MamedeConditionalConverse
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
from any nonempty reduced consecutive word. In the first orientation,
`MamedeNonoscSourceEndpoints.first_orientation_strict_endpoints` now derives
strictly interior endpoint indices and both remaining position equations from
an actual nonoscillating source. No source shape is assumed. The indices may
occur in either order; the conditional `j<i` fiber step is proved below.
The reflected theorem starts from `sigma(m)=M+1` with the same actual word
and interval data, proves `m<M`, and returns strict interior `i,j` with
`sigma(j+1)=m`, `sigma(M+1)=i`, and exterior fixedness. Its reusable
`word_reversal_invariants` input preserves the exact singleton and oscillation
predicates under word reversal and permutation inversion, including empty
and singleton lists. No source shape or extra position equation is assumed.
These source results do not change KPI.

`MamedeEndpointUniqueness.extremal_endpoint_unique` proves that two reduced
consecutive words with the same product and the same first (or the same
last) letter are equal when that letter is a minimum of both words or a
maximum of both words. This formalizes the endpoint uniqueness ingredient
of Lemmas 3.2 and 3.4. Together with the endpoint assumptions in the
conditional fiber theorem below, it helps identify all words in a `j<i`
fiber. It does not change KPI.

`MamedeEndpointUniqueness.maximum_peel` makes the existing initial-descent
proof reusable: a reduced consecutive word beginning at its attained maximum
is a full descent to `i` followed only by generators greater than `i`.
The new `extremal_endpoint_oscillation` proves the endpoint-to-oscillation
direction for the exact Lean predicate: the first or last letter is an attained
minimum or maximum, with reducedness and consecutive indices unchanged.
It identifies the peeled runs with `spikes` and proves weakly decreasing
segment lengths for a first extremum. Reversal gives the last-letter cases.
This is a source-only result; it does not close the source adapter or change KPI.

`MamedeEndpointUniqueness.symmetric_excursion_outer_empty` proves the
reducedness obstruction for an actual central word that descends from `M` to
`m` and ascends back to `M`. When both outer factors use only interior
generators, consecutiveness forces `M-1` on their adjacent ends; the central
product swaps the two exterior positions and commutes with that generator,
so the bracketing copies cancel. Hence at least one outer factor is empty.
This theorem does not assume either endpoint equation and does not extract
the central factorization from them. KPI remains 0.

`MamedeEndpointUniqueness.opposite_extremal_maps_oscillation` supplies that
extraction and its oscillation consequence for an explicit attained generator
interval. For `singletonWord n sigma a`, attained `m,M`, `1<=m<=M<=n`,
and support in `[m,M]`, the simultaneous maps `sigma(M+1)=m` and
`sigma(m)=M+1` imply `oscillation a`. The proof handles `m=M` directly.
For `m<M` it forces a descent in the word and its reverse, aligns the resulting
descent and ascent at `m` or `M`, and proves interior support for both outer
factors. The symmetric-excursion obstruction and its reflected application
then give an attained minimum or maximum at a word endpoint. Neither
oscillation, source shape, nor an endpoint is an input. This closes the
opposite-map consumer under its exact support hypotheses; KPI remains 0.

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

Both extremal-orientation endpoint adapters are compiled. For the first
orientation, with attained `m,M`, support in `[m,M]`, nonoscillation, and
`sigma(M+1)=m`, the indices satisfy
`m<i<M` and `m<j<M`, both required position maps, and exterior fixedness.
For `i<=j`, these are the endpoint premises of the existing shape and deletion
results; for `j<i`, they are the premises of the existing whole-fiber
uniqueness theorem. In the reflected orientation, assuming `sigma(m)=M+1`
gives `sigma(j+1)=m` and `sigma(M+1)=i` with the same strict bounds.
Those maps become the first-orientation inputs for `sigma^{-1}` and the
nonoscillating word `a.reverse`. The `i<=j` branch supplies the exact
inverse-permutation deletion hypotheses; the `j<i` branch supplies
whole-fiber uniqueness, transported back by reversal. Neither adapter orders
`i,j` or proves the oscillating and involutive branches, terminating cases,
or a global count argument for every permutation.
The class-to-word correspondence and the paper's upper bound still require
formal justification in this adjacent-word model before the full conjecture
can be claimed. Research target: [#10285](https://github.com/the-omega-institute/trureturing/issues/10285).

## Route

Assemble the reflected deletion branch in the original permutation convention
(the inverse deletion target `sigma^{-1} * gamma^{-1}` reverses to
`gamma * sigma`, with `gamma` the deleted-excursion product), and the
oscillating and involutive cases, handle the terminating cases, justify the class-to-word correspondence
and upper bound in the formal model, and close the global induction.

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
theorem. The reflected endpoint extraction is compiled; the reflected
deletion assembly, oscillating, involutive, and global count cases are not
claimed as completed here.
