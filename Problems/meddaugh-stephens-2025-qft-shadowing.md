---
slug: meddaugh-stephens-2025-qft-shadowing
bibkey: meddaugh2025neighborhoodshadowing
doi: null
url: https://arxiv.org/abs/2509.04312v1
triage: theorem
motivation_gids:
  - D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_twoTailShadowing
---

# Two-tail shadowing for quasi-finite type

## Problem

Jonathan Meddaugh and Elyssa Stephens, *Shadowing with small diameter sets
of bounded cardinality*, arXiv:2509.04312v1, Question 5.4:

> Can being a subshift of quasi-finite type be reasonably characterized as a form of shadowing in subshifts?

Definition 3.5 requires a uniform threshold such that if legal words
$uw$ and $wv$ share a bridge $w$ at least as long as the threshold,
some replacement of length $|w|$ gives a legal concatenation of $u$,
the replacement and $v$. [Question 5.4](https://arxiv.org/html/2509.04312v1#S5.Thmtheorem4)

## Motivation

The exact replacement length calls for a tracing orbit at the original
times. A trace of two infinite tails retains the exterior contexts
while leaving room for a replacement near the jump.

## Gap

The primary paper derives neighborhood two-shadowing from quasi-finite
type. Question 5.4 asks for a shadowing condition that also implies
quasi-finite type.

## Route

In a two-sided finite-alphabet subshift, take the past of one point
and the future of a sufficiently close point. For each tracing accuracy,
choose the input tolerance and a uniform cutoff. The condition asks
one true orbit to trace both tails at the original times outside the
interval set by the cutoff.

Quasi-finite type gives finite replacements of the common central
block. Apply it to increasing exterior contexts. The sets of points
tracing these finite contexts are nonempty, closed and nested.
Compactness gives one point realizing both infinite tails. A larger
cutoff accounts for the finite coordinate window that controls the
tracing accuracy.

Conversely, choose an accuracy that detects coordinate zero. Align
occurrences of the two legal words around the center of their common
bridge. A sufficiently long bridge ensures a small jump and puts both
exterior contexts outside the untraced interval. Reading the tracing
point on the original bridge positions supplies the required exact
length.

## Falsifier

A counterexample to the forward implication would be a quasi-finite-type
shift with, at some accuracy, arbitrarily close pairs that defeat every
uniform cutoff. A counterexample to the reverse implication would satisfy
the stated tail tracing while still having common bridges of unbounded
length with no legal replacement of the same length.

## Evidence

The Lean theorem
`D5/S1/Dynamics/Shadowing/QuasiFiniteType.quasiFiniteType_iff_twoTailShadowing`
uses the compact product topology and a fixed tracer for both tails.
The metric is any genuine compatible metric on the subshift.
[Library source note](../Library/Dynamics/meddaugh2025neighborhoodshadowing.md)

The information-escape registrations are still open under
[issue #32325](https://github.com/the-omega-institute/trureturing/issues/32325).

## Triage

The condition gives a dynamical characterization in the two-sided
setting. It is preserved by topological conjugacy since the maps and
their inverses are uniformly continuous on the compact subshifts.

## ASSUMED-UNVERIFIED

The bounded literature comparison covered local product structure,
stable–unstable intersection and two-sided limit shadowing. The full
text of Stephens's dissertation remains unavailable for comparison.
