---
slug: manna-mandal-tura-2026-cograph-distance-left-gap
bibkey: mannamandaltura2026cographdistance
doi: null
url: https://arxiv.org/pdf/2611.06981v1#page=22
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.result
---

# The distance spectrum of connected cographs has no uniform left gap at −2

## Problem

Pallabi Manna, Santanu Mandal and Fernando C. Tura, *The Spectral Theory of
Cographs: A Survey, Organized by Graph Matrix*, arXiv:2611.06981v1,
Open Problem 14.2(i), printed p. 22, asks

> Is there ε > 0 such that (−2 − ε, −2) contains no distance eigenvalue of any connected cograph?

The [Library note](../Library/QuadraticForms/mannamandaltura2026cographdistance.md)
records the pinned source. The exact positive assertion and the
counterexample criterion are recorded in the
[Tier 1 issue](https://github.com/the-omega-institute/trureturing/issues/32278)
and its [preregistration](https://github.com/the-omega-institute/trureturing/issues/32278#issuecomment-7041178969).

| Source clause | Lean counterpart |
| --- | --- |
| One positive real width for every connected cograph | An outer `∃ ε : ℝ` with `0 < ε`, followed by all `SimpleGraph V` with `[Fintype V]` and `G.Connected` |
| Finite simple graph free of induced four-vertex paths | `P4Free G = IsEmpty (SimpleGraph.pathGraph 4 ↪g G)`, using an injective relation embedding that preserves and reflects adjacency |
| Distance matrix | `distanceMatrix G x y = (G.dist x y : ℝ)`, native shortest-path edge counts with diagonal zero |
| Distance eigenvalue | `Module.End.HasEigenvalue (distanceMatrix G).mulVecLin λ`, equivalent to a nonzero real vector satisfying `D(G) *ᵥ v = λ • v` |
| Open interval | The claim excludes the conjunction `-2 - ε < λ ∧ λ < -2` |
| Outcome | `result : ¬ claim` |

## Motivation

The survey gives the right-hand gap from Lou–Lin and cites a larger excluded
interval for nontrivial eigenvalues of threshold graphs. The uniform left
gap for all cographs concerns whether −2 is an accumulation point from below
as the graph order increases.

## Gap

Section 6.1 provides the numerical example K₁ ∨ (K₁ ∪ 3K₂), which witnesses
failure at one width. The question quantifies over every positive width.
The bounded pre-probe literature screen found the question in the pinned
survey and no exact settlement within the inspected sources. It distinguished
the threshold subclass result, the Lou–Lin right gap, and repository work on
the distance signless Laplacian.

## Route

Let Gᵣ = K₁ ∨ (K₁ ∪ rK₂). The universal vertex connects all vertices.
Every vertex of an induced four-vertex path has a nonneighbor within that
path, so such a path misses the universal vertex. Away from that vertex,
the maximum degree is one. The native distances are zero on the diagonal,
one on edges and two between distinct nonadjacent vertices.

The vectors constant on the universal vertex, the initially isolated
vertex, and the matching endpoints carry the quotient with rows
(0, 1, 2r), (1, 0, 4r), and (1, 2, 4r−3). With t = λ+2, its shifted
determinant is (t+1)(t−1)(t−3)+(6−4t)rt. It equals 3 at t=0. For every
positive integer q, choose r=q. At t=−1/q the determinant is
−((1+1/q)³+2). The intermediate value theorem and the two nonzero
endpoint values give a root strictly between the endpoints. A nonzero
quotient kernel vector lifts to a nonzero distance eigenvector, since
each of the three orbits is nonempty. Choose q with 1/q<ε.

## Falsifier

An induced four-vertex path in the family, a discrepancy between its native
distances and the quotient action, a failure of either strict determinant
sign, or a vanishing lift of the nonzero kernel vector would defeat the
construction. The Lean proof discharges each obligation for every required
positive integer parameter.

## Evidence

The settling Lean module is
`D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraCographDistanceGapRefutation.lean`.
Its public family theorem is `registered_family_counters_gap` and its
refutation endpoint is `result`. The strict quotient root lies on both
theorems’ proof paths. Both import pinned Mathlib through the settling
module, with no frozen D5 prerequisites. The admission basis is
`open-problem-resolution` for Tier 1 issue #32278.

The source binding for `registered_family_counters_gap` observes the lower
endpoint −2−ε at the original real width ε. Replacing that readout by the
constant −2 makes the strict interval empty. The checked binding preserves
the remaining source clauses and records an unknown continuation.

## Triage

### What the settlement shows

| Finding | Status |
| --- | --- |
| Every positive ε admits a distance eigenvalue of Gᵣ strictly between −2−ε and −2 | Kernel-checked by `registered_family_counters_gap` |
| A single positive width works for every connected cograph | Refuted by kernel-checked `result` |
| The distinct right gap (−2,−1) | The pinned survey states it as Theorem 6.5, attributing it to Lou–Lin |
| Characterize equality in the distance-eigenvalue multiplicity bound and give an infinite attaining family, Open Problem 14.2(ii) | Separate open question in this dossier |

The mechanism is an exact sign change over widths 1/q in graphs of
unbounded order. The signs locate the root strictly below −2 and below
the right-hand gap.

## ASSUMED-UNVERIFIED

Completeness of the literature search outside the inspected arXiv material
and citation metadata is unverified. The inspected publisher route supplied
the Lou–Lin abstract without the full text. This dossier settles part (i)
of the pinned version.
