---
slug: verkama-2026-conjecture-62
bibkey: verkama2026connectivity
doi: 10.48550/arXiv.2611.17237
url: https://arxiv.org/html/2611.17237v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/Verkama62Result.result
---

# Verkama Conjecture 6.2

## Problem

Emil Verkama, *Permutation patterns and higher connectivity in inversion graphs*,
arXiv:2611.17237v1, Section 6, Conjecture 6.2, states:

> Every permutation π ∈ Av(351624) whose inversion graph is 2-connected satisfies inv(π) ≥ (7/4)|π| − 3.

The exact locator is
https://arxiv.org/html/2611.17237v1#S6.Thmtheorem2.
The original preregistration is
[#30964](https://github.com/the-omega-institute/trureturing/issues/30964).
The target, before-probe predictions and deadline in that preregistration are
unchanged. This dossier concerns one assertion and one complete proof.

### Statement echo

For every natural number n and every permutation π of n elements, assume n ≥ 3,
classical avoidance of 351624, and ordinary vertex-2-connectivity of its inversion
graph. Then 7n ≤ 4 inv(π) + 12, equivalently inv(π) ≥ (7/4)n − 3 in the rationals.

| Source clause | Formal counterpart |
| --- | --- |
| Every finite permutation | `n : Nat`, `pi : Equiv.Perm (Fin n)` |
| Classical 351624 avoidance | `¬ ContainsOneBased pi`; six increasing positions with relative value order `[3,5,1,6,2,4]` |
| Value-labelled inversion graph | `valueGraph pi`; adjacency is a strictly negative integer product of value and inverse-position differences |
| Ordinary vertex-2-connectivity | `3 ≤ n`, graph connected, and induced singleton complement connected for every vertex |
| Inversion number | Existing `FranklinInversionDefs.inv (PSW.word pi)`, identified with the increasing-position inversion count by `word_inversions` |
| Exact bound | `result` proves the rational inequality `(7/4)*n-3 ≤ inv` |

Source labels are obtained from `Fin n` by adding one. The pattern bridge uses
the existing zero-based containment predicate with `[2,4,0,5,1,3]`.
There is no extra ear, geometry, stronger avoidance, bipartiteness, finite cutoff
or asymptotic hypothesis.

## Motivation

The source separately states the seven-quarters bound after its general
three-halves bound. The earlier Linusson–Verkama Theorem 8 on almost decomposable
1324-avoiders and Verkama's thesis Conjecture 5.0.4 concern different assertions.
The source/version and those distinctions are recorded in #30964 and the
[source note](../Library/PermutationPatterns/verkama2026connectivity.md).

## Gap

The inspected original-paper, arXiv-version, author-linked and repository scopes
did not identify a complete prior resolution of this exact assertion. That is
bounded search evidence. Worldwide unresolvedness, priority and completeness of
the literature screen are `ASSUMED-UNVERIFIED`; no originality or priority claim
is inferred from a negative search. Failed Semantic Scholar/OpenAlex and Scholar
requests supplied no forward-citation evidence.

## Route

The [settling module](../D5/S3/Combinatorics/Permutation/Verkama62Result.lean)
proves `D5.S3.Combinatorics.Permutation.Verkama62Local.result`.
Ordinary connectivity after every single deletion first supplies an anchored
triangle or 3412 square. Boundary walks and the two original extreme points
give singleton or northeast double extensions. Deletion robustness and strong
induction on the number of missing points construct a complete ear run without
using avoidance.

The avoidance argument then controls the signed potential 7|V|−4|E|. A fresh
terminal 3412 persists through zero or one singleton of old degree two; a
subsequent cheap double extension forces a classical 351624 occurrence.
The resulting run invariant bounds the potential by 12. The inversion-count
representation and exact rational transport yield the stated bound.

All nine supporting modules are on this proof's live dependency path. Consumed
normalization helpers are proof organization and supply no separate solution
credit. The endpoint is `content` after inlining same-delivery helpers;
`admission_basis: open-problem-resolution` refers to the original #30964 target.
Existing containment, permutation-word and inversion-counter definitions and
pinned Mathlib order, finite-sum and graph facts are reused. No prior exact
target theorem was found in that inspected scope.

## Falsifier

A counterexample would satisfy exactly the classical avoidance and ordinary
vertex-connectivity hypotheses while having 7n > 4 inv(π) + 12. The complete
theorem excludes such a permutation without imposing a length bound.

## Evidence

The complete proof is kernel-checked with axiom closure contained in
`propext`, `Classical.choice` and `Quot.sound`. It covers every source length and
all stated hypotheses; finite examples alone are not the proof.

Fifteen public-theorem audit attempts compile. Seven have validated bindings;
eight remain unfinished under
[#31005](https://github.com/the-omega-institute/trureturing/issues/31005):
`anchored_extension`, `PairEar.to_double`, `value_adj`, `anchored_start`,
`Terminal.forces`, `Fresh.no_cheap_double`, `complete_run` and `EarRun.robust`.
Their inspector finding is `IE-C050 ClosedTruthReadout / unclassified_form`.
`PairEar.to_double` lacks `source.state_operand_path`; the other seven lack
`source.observation_data`. The retained attempts and successful evidence are
preserved. The linked issue supplies neither proof nor validated audit status.

## Triage

The formal result proves the complete stated inequality. The supporting
geometry and potential invariant are part of this one proof, not additional
open-problem settlements. Eight audit bindings remain unfinished as specified
above. Final independent triplet, exact required CI and normal merge remain
delivery obligations.

## ASSUMED-UNVERIFIED

Worldwide novelty, priority and literature completeness are unverified. This
mathematical result does not certify complete audit validation, final independent
triplet approval, required CI, merge or FirstDEV.
