---
slug: feldman-wilce-bounded-cliques-open-chromatic-strictness
bibkey: feldmanwilce2026compactnesscliques
doi: 10.48550/arXiv.2608.13320
url: https://arxiv.org/html/2608.13320v1
triage: theorem
motivation_gids:
  - D5/S3/Topology/StoneCech/DeletedSquareChromatic.result
---

# Feldman–Wilce Question 2: bounded cliques versus finite open chromatic number

## Problem

David V. Feldman and Alexander Wilce, *A Note on Compactness and Clique Size*,
arXiv:2608.13320v1, Section 5, Question 2:

> Is the second implication strict?

The displayed implications are compactness implies the finite open chromatic
property implies the bounded clique property. Both graph properties quantify
over every symmetric irreflexive relation closed in the entire product.
Finite open chromatic number means a finite cover by open independent sets;
the sets may overlap. A bounded clique conclusion must bound all clique
subsets and in particular exclude infinite cliques.

## Motivation

An affirmative answer requires an actual Hausdorff space with the universal
bounded clique property and one whole-product closed orthogonality admitting
no finite open independent cover. The Question 1 section-selector construction
does not settle this question.

## Gap

The concrete witness is the deleted square of the Stone space of ultrafilters
on Nat, with its induced product topology. The theorem `result` proves
Hausdorffness, the bounded clique property for every closed orthogonality,
and failure of the finite open chromatic property. The graph used for failure
is the coordinate swap. No additional set-theoretic hypothesis is present.

## Route

For arbitrary compact Hausdorff extremally disconnected K, native clopen
point-pair separation and diagonal thinning put a cluster point of any
sequence in the countable power of its deleted square inside every required
off-diagonal clopen cylinder. Compactness is used only in the ambient product.
The native inducing product embedding transfers this cluster point back.

The Feldman–Wilce countable-power criterion is implemented independently
from the mathematical argument. Unbounded finite cliques give a sequence
in the countable power whose cluster point has pairwise adjacent coordinates.
A cluster point of those coordinates gives a diagonal point in the closed
relation, contradicting irreflexivity. Infinite clique subsets are separately
excluded; their ncard value cannot conceal them.

For the swap graph on the deleted square of beta Nat, color unordered
principal pairs by both full finite-cover membership patterns. The native
Apache-2.0 infinite Ramsey theorem gives homogeneous directional patterns,
which independence makes disjoint. Two free ultrafilters on disjoint infinite
homogeneous supports give a cover member containing a clopen rectangle.
Both orders of natural principal pairs occur inside it, forcing its color
into both disjoint patterns.

## Falsifier

Any extra CH or MA premise, missing infinite-clique case, closedness only
off the diagonal, sequential compactness substituted for countable
compactness, restricted relation quantifier, or disjointness assumed for the
finite open cover would invalidate the correspondence.

## Evidence

The full mathematical module passed the native scoped Lean build. The
compiler's axiom closure for each of its four public theorems, including
`result`, is exactly `propext`, `Classical.choice`, and `Quot.sound`.
Native statement and axiom reports supply the formal verification evidence;
official CI and final independent source-fidelity review are separate.

The inspected primary version still asks Question 2. The author repository
at `1f4da701cfb6d7588a90f005fa83698e3a1b081b` marks `ChromaticQuestion` open.
The bounded source and literature checks did not locate a subsequent
solution, with broad search engine and API limitations disclosed. This is
not a global novelty guarantee.

## Triage

Tier 1 published end-of-paper question. The public `result` is the exact
registered external open-problem resolution. Its admission basis is
`open-problem-resolution`; its proof has content through the countable-power
deleted-square construction and the full-pattern Ramsey obstruction.
The other declarations are used on its live proof path. The countable-power
criterion is an attributed known theorem, implemented independently rather
than copied from the unlicensed author repository.

## ASSUMED-UNVERIFIED

Worldwide absence of earlier solutions, publication priority, acceptance by
the original authors, official CI, and final independent formal-source review
are not established by the local Lean build.

The retained four-slot registrations for `no_finite_open_independent_cover`
and `result` are `declared_unresolved`: the native reader reports
`IE-C050 ClosedTruthReadout`, respectively `rule=source.operand_mode` and
`rule=source.definition_type`. Their complete typed source bridges compile.
The complete typed families for `countablyCompactSpace_deletedSquare_power`
and `boundedCliqueProperty_of_countablyCompact_power` also compile, but their
attempted polymorphic Contract records encounter
`contract.discovery:rigid_universes` and are not retained as active records.
The missing evidence is native validated template/source-selection binding
for all four public theorems. This unfinished audit is disclosed under the
linked-issue exception at
https://github.com/the-omega-institute/trureturing/issues/29397;
the issue is not audit validation or mathematical proof. No judge change or
weakening of a theorem is used to obtain a different audit status.
