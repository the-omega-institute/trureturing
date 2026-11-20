---
slug: meddaugh-stephens-2025-shadowing-language
bibkey: meddaugh2025neighborhoodshadowing
doi: null
url: https://arxiv.org/abs/2509.04312v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Shadowing/LanguageCharacterization.neighborhoodFiniteShadowing_iff_languageColoring
---

# A finite-language criterion for neighborhood shadowing

## Problem

Jonathan Meddaugh and Elyssa Stephens, *Shadowing with small diameter sets
of bounded cardinality*, arXiv:2509.04312v1, Question 5.5:

> Can neighborhood 2-shadowing in subshifts be reasonably characterized by the language of a subshift?

The source uses finite alphabets and two-sided configurations.
Its Definition 2.1 uses natural-time pseudo-orbits, a fixed finite
tracing set and an initial diameter bound. [Question 5.5](https://arxiv.org/html/2509.04312v1#S5.Thmtheorem5)

## Route

For each tracing radius $k$, choose one local radius $m\geq k$ before
choosing a horizon $n$. Take any word on $[-m,n+m]$ whose centered
radius-$m$ blocks at times $0,\dots,n$ occur in the language.
The criterion is that the times $1,\dots,n$ can be colored using $N$
colors. Each color class must have a language extension on $[-k,n+k]$
agreeing with the given word on $[-k,k]$ and on every radius-$k$ block
in that class, including the requirement at time zero for empty classes.

For necessity, realize each locally legal block as a subshift point,
then append the true orbit of the last point. A small-diameter tracing
set matching at time zero puts every tracer in the initial cylinder.
Choose the color of each positive time by a tracer that covers it.
For sufficiency, glue the overlapping blocks of the pseudo-orbit.
For each finite horizon the criterion supplies a tuple of tracers.
The feasible tuples form a decreasing sequence of nonempty closed
sets in the compact tuple space. Their intersection supplies a fixed
tuple that traces at all times.

## Evidence

The Lean theorem
`D5/S1/Dynamics/Shadowing/LanguageCharacterization.neighborhoodFiniteShadowing_iff_languageColoring`
gives the equivalence for every positive finite $N$ and every compatible
metric. The endpoint reuses the project's `NeighborhoodFiniteShadowing`
predicate. Inclusion-minimal nonextendible sets of times give the forbidden
hyperedges, so the finite test is an $N$-coloring with no monochromatic
forbidden edge. [Library source note](../Library/Dynamics/meddaugh2025neighborhoodshadowing.md)

The information-escape registrations are still open under
[issue #32288](https://github.com/the-omega-institute/trureturing/issues/32288).

## Triage

Taking $N=2$ answers Question 5.5 in the source's setting. The finite test
uses only membership in the subshift language. Decidability and an a priori
bound on the tested horizons are separate questions.

## ASSUMED-UNVERIFIED

No equivalent prior result was found in the inspected sources. The full
text of Stephens's dissertation remains unavailable for comparison.
