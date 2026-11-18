---
slug: meddaugh-stephens-2025-neighborhood-shadowing-hierarchy
bibkey: meddaugh2025neighborhoodshadowing
doi: null
url: https://arxiv.org/abs/2509.04312v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy
---

# The finite neighborhood-shadowing hierarchy

## Problem

Jonathan Meddaugh and Elyssa Stephens, *Shadowing with small diameter sets
of bounded cardinality*, arXiv:2509.04312v1, Questions 5.1 and 5.2:

> For which N are there dynamical systems with neighborhood (N+1)-shadowing, but not neighborhood N-shadowing?

> For which N are there subshifts with neighborhood (N+1)-shadowing, but not neighborhood N-shadowing?

The preceding paragraph explicitly says the authors had not found a system
or subshift with neighborhood three-shadowing but not neighborhood two-shadowing.
Definition 2.1 requires one fixed nonempty finite tracing set with small
initial diameter. Ordinary finite-cardinality shadowing omits the latter
condition and does not answer these questions.

## Motivation

Strict finite levels separate the number of whole orbits needed to trace
an infinite pseudo-orbit even when those orbits begin arbitrarily close.
The construction gives every positive finite level on a binary two-sided
subshift, including the first three-but-not-two case.

## Route

For m>=3 let X_m contain precisely the configurations x in {0,1}^Z such
that every m-term progression of step (m+1)^k, for k>=0, contains at most
two ones. In Lean this is the equivalent prohibition of three distinct
occupied vertices. The constraint is closed and invariant under every
integer shift. The zero point gives nonemptiness. The shift by one is
continuous and has the shift by minus one as its inverse. The metric is
Mathlib's genuine compatible countable-product metric, inherited by X_m.

For an accuracy window, choose a large power Q=(m+1)^K. There are m-1
periodic phase masks with a common initial window, such that each future
window is entirely retained by some mask. Each mask retains at most two
vertices of every translated regular m-gon. For k>=K, the progression
phases reduce to that polygon because (m+1)^(k-K) is one modulo m.

The signed diagonal of a sufficiently accurate natural-time pseudo-orbit
agrees with the observed windows. Its short progression constraints are
already legal. Deleting its ones outside each mask makes every long
constraint legal too. The resulting m-1 whole configurations form one
fixed finite tracing set with small initial diameter. The selected member
can vary with time; the set does not.

For the lower bound, fix one positive accuracy forcing coordinate-zero
agreement. At every tolerance, take a large q=(m+1)^k and locally truncate
the support {0,q,...,(m-1)q}. Each state has at most one one and is legal;
the sequence is a pseudo-orbit at the requested tolerance. Initial tracing
and small initial diameter force every tracer to have a one at zero.
Its progression constraint leaves capacity for at most one of the m-1
future target coordinates. Thus at least m-1 tracers are necessary.

Taking m=N+2 gives neighborhood (N+1)-shadowing and failure of
neighborhood N-shadowing for every N>=1.

## Falsifier

The endpoint would fail if the masks only controlled unshifted polygons,
if negative initial coordinates were omitted, if the tracing set changed
with time, or if the lower bound excluded only a proposed choice of
tracers. The finite-set predicate includes nonemptiness, cardinality,
initial diameter and distance to every natural-time image. The final
theorem constructs the subshift and assumes no mask or count supplier.

## Evidence

The endpoint is
`D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy.lacunary_shadowing_hierarchy`.
Its supporting modules are `LacunaryPhaseCover`,
`LacunaryProgressionSubshift`, `LacunaryShadowingLower` and
`LacunaryShadowingUpper`, with corresponding Blueprint Scribe sources.
The complete endpoint has passed a scoped Lean build. Canonical freezing
and required repository checks remain separate delivery obligations.

The construction and its complete ordinary mathematical proposal are
attributed to Pro through the oracle broker; Codex implemented the proofs.
The exact target was preregistered in
[issue #31384](https://github.com/the-omega-institute/trureturing/issues/31384).

## Gap

The mathematical endpoint covers every positive finite N. It asserts small
initial diameter only, as in the source; it does not assert small diameter
of all later image sets, ordinary single-orbit shadowing, or any infinite
cardinality hierarchy.

Faithful four-slot information-escape registration is unfinished under
issue #31384. Source-law attempts are not `Contract.Registration` values
or `declared_validated` evidence. Enrolled source reconstruction,
whole-family variation and sensitivity, observational dependence and
lawful readout binding remain missing.

## Triage

The inspected primary v1 poses both questions; the construction supplies
all positive finite levels in binary subshifts. A bounded literature search
found no exact prior answer, which is not an exhaustive priority exclusion.
Baylor's November 6, 2026 announcement confirms Ellie Stephens' dissertation
*Local Variations of Shadowing*, advised by Jonathan Meddaugh. Its summary
concerns neighborhood shadowing, but does not state a hierarchy theorem;
the full dissertation was unavailable. Whether it contains an earlier
answer remains unverified.

## ASSUMED-UNVERIFIED

The primary correspondence uses Definition 2.1's fixed finite tracing set
and initial diameter, with a genuine compatible product metric. The
inspected primary v1 poses Questions 5.1 and 5.2. The full Stephens
dissertation and exhaustive worldwide priority comparison remain
unverified; the announced defense is not a theorem-level comparison.
Native Lean proofs and canonical freezes do not assert remote CI success,
merged publication, unique status or completed four-slot registration.
