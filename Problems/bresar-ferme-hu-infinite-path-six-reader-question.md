---
slug: bresar-ferme-hu-infinite-path-six-reader-question
bibkey: bresar2026packingdomatic
doi: 10.48550/arXiv.2610.03477
url: https://arxiv.org/abs/2610.03477v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result
---

# Six broadcast-dominating packing classes on the two-way infinite path

## Problem

Brešar, Ferme and Hu, *Partitioning an S-packing coloring into broadcast dominating sets*,
arXiv:2610.03477v1, Section 3.2, immediately after Theorem 3.6, ask:

> For k=6, the problem is reduced to determining which of the two possible values in {4,5} is attained by χ_{ρ,6}(P∞), a question we leave for the reader.

The graph P∞ has vertices Z and distance |u-v|. For t in Nat, Q(t) asserts the existence of
f:Z→Nat and one common c:Z→Fin 6 such that 1≤f(x)≤t for every x, distinct vertices of the
same colour j are at distance greater than j, and for every x and every class i there is a
vertex a with c(a)=i and |x-a|≤f(a). Neither map is assumed periodic or regular.
The exact answer is 5: Q(5) holds, and Q(t) implies 5≤t for every natural t.

## Motivation

The source gives a five-colour upper construction but leaves the exact six-class value to the
reader. The complete unrestricted resolution is the conclusion of
`D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result`.
This question is distinct from the paper's finite-path Problem 2.

## Gap

A periodic obstruction alone would not exclude arbitrary infinite realizations. The lower
argument instead restricts any purported realization to a finite observation window without
assuming any repeating pattern.

## Route

For the upper bound, consume the source's repeating colour pattern [5,1,2,4,1,3] and its
period-30 partition. A local certificate supplies covering offsets for all 30 residues and
all six classes; a universal integer-translate bridge establishes broadcast domination
on all of Z. For the lower bound, compare forced domination incidences with packing capacity
on two nested finite integer intervals. Palette monotonicity excludes every smaller palette.

## Falsifier

A realization satisfying Q(4), or a failure of the asserted upper witness on any integer,
would contradict the displayed result. A finite-path example, a periodic-only exclusion,
or an unchecked local numerical table would not settle this question.

## Evidence

The exact Lean conclusion is `Q 5 ∧ ∀ t : Nat, Q t → 5 ≤ t`, in the namespace
`D5.S3.Combinatorics.PackingDomatic.PackingDomaticInfiniteSix`.
Theorem 3.6's upper construction is an attributed prior ingredient; the unrestricted
lower obstruction completes the reader question.

The bounded literature screen covered the original HTML/TeX, arXiv version and relation
information, author/index/citation searches, and the distinct finite-path resolution.
No exact subsequent solution was found within that scope. Author-hosted pages, a related
thesis full text, and inaccessible or unindexed material were outside that screen;
worldwide priority is not asserted.

## Triage

### What the settlement shows

Proved by `D5/S3/Combinatorics/PackingDomatic/PackingDomaticInfiniteSix.result`: the least
six-class palette on the two-way infinite path is exactly 5, uniformly over arbitrary
infinite realizations. The decisive lower obstruction uses J=[0,999] and I=[4,995]. The six
classes require at least 6·992=5952 incidences. Strict same-colour separation makes the maps
a↦a/(j+1) injective on vertices of colours j=2,3,4. Their count bounds 334,250,200 give
capacity at most 3·1000+2·334+4·250+6·200=5868, a contradiction with gap 84.
These bounds and the all-integer bridges occur in the proof of the same result.

The upper case Q(5) is attained by the source's construction, so the bound is tight at 5.
Every smaller natural palette is excluded by the same result and its palette-monotonicity
step. The conclusion concerns the two-way infinite path and the exact six-class reader
question in arXiv:2610.03477v1. It adds no finite-path conclusion and settles no case k≥7.

A precise unproved successor is to determine χ_{ρ,7}(P∞), the least positive bounded
palette admitting a packing colouring on Z and one common seven-class map whose every
class dominates every integer at the broadcaster's own colour radius. A settlement needs
an attained upper construction with packing verified for all pairs and domination verified
for all integers and classes, together with a matching lower obstruction for arbitrary
infinite realizations. Any finite certificate needs a proved all-integer extension; a
periodic-only exclusion does not supply the required lower bound. No such matching pair
of bounds is established here.

## ASSUMED-UNVERIFIED

The bounded source screen does not establish exhaustive priority across inaccessible or
unindexed literature. The seven-class successor and the other cases k≥7 remain unproved
by this result.
