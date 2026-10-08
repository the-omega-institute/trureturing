---
slug: filimonova-puzynina-2026-rank-one-iteration-bound
bibkey: filimonovapuzynina2026abelianperiodicity
doi: null
url: https://arxiv.org/abs/2605.30306v1
triage: theorem
motivation_gids:
  - D5/S1/Words/RankOneMorphismIterationBound
---

# Filimonova–Puzynina's rank-one iteration-bound question

## Problem

Filimonova and Puzynina ask in Section 4 of *On abelian periodicity of purely
morphic words* (arXiv:2605.30306v1) whether the iteration variable in their
primitive binary rank-one criterion has an upper bound making the criterion
algorithmic.

The source's fixed word is allowed an arbitrary finite preperiod.  The target
is the complete nonerasing, prolongable, primitive, rank-one binary domain,
with exact Parikh equality in the cyclic block witness.

## Motivation

The question asks for an effective version of the source criterion.  A total
bound from the two actual image lengths also gives a finite decision procedure
for eventual abelian periodicity.

## Gap

The source states the criterion but leaves the iteration bound open.  The
preregistration and bounded prior-art screen are recorded in issue [#13429](https://github.com/the-omega-institute/trureturing/issues/13429).

## Route

The proof extracts the coprime rank-one parameters, presents the actual
iterates through a finite uniform expansion, and encodes cyclic witnesses as
constant-output subset paths.  There are at most
`2^(|f(0)|+|f(1)|)` subset states, so any accepted path can be shortened to
that bound.  Height rays and recurrent source residues establish the reverse
direction for arbitrary preperiods and retain the original cyclic witness.

## Falsifier

A morphism satisfying the complete source hypotheses with an ultimately
abelian-periodic fixed word but with no witness at any
`1 ≤ K ≤ 2^(|f(0)|+|f(1)|)` would refute the result.  A witness using a proxy
fixed word, pure periodicity, a fixed-K hypothesis, or a frequency-only
equivalence would not address this problem.

## Evidence

`D5/S1/Words/RankOneMorphismIterationBound.effective_iteration_bound` proves
the full bounded equivalence.  `finiteChecker_uap` proves correctness of the
executable finite-image checker for the same domain.  The source modules and
their exact-type importing clients compile under the pinned Lean/Mathlib
environment; the importing client's axiom closure is only
`propext`, `Classical.choice`, and `Quot.sound`.

The source module and its proof dependency closure are registered in the
Frozen state.  The canonical Scribe description binds the `Proved` resolution
to `effective_iteration_bound`.  Issue #13429 records the preregistration and
the complete kernel-checked evidence; issue [#14423](https://github.com/the-omega-institute/trureturing/issues/14423)
tracks completion of the missing publication records.

## Triage

`theorem`; the formal result settles the registered iteration-bound question
on the complete source domain.

## ASSUMED-UNVERIFIED

The literature screen is bounded by the searches recorded in issue #13429.
It does not establish worldwide absence or priority.
