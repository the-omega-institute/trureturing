---
slug: arvind-2023-commuting-graph-q4
bibkey: arvind2023commuting
doi: 10.48550/arXiv.2305.07301
url: https://arxiv.org/abs/2305.07301v5
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.result
---

# Non-isoclinic commuting-graph pairs at every prime-sixth order

## Problem

The second sentence of Section 9, Q4, page 40 of Arvind–Cameron–Ma–Maslova,
*Aspects of the commuting graph*, arXiv:2305.07301v5, asks:

> Do non-isoclinic examples exist for all orders $p^6$ with $p$ prime?

For every natural prime, including two, the target is two finite groups of
that order with isomorphic full simple commuting graphs and no compatible
central-quotient and derived-group isomorphisms intertwining the source
commutators. The first, broader sentence of Q4 is not the target.

## Motivation

The graph retains exactly which pairs commute. Isoclinism additionally
retains the group structure on the derived subgroup and compatibility with
the central quotient. The question asks whether this extra information can
be lost at the specified order uniformly in the prime.

## Gap

The source supplies primes two, three and five. A uniform construction
requires an all-pairs incidence bijection and a compatible obstruction for
the same two groups at every prime.

## Route

Put R equal to ZMod(p*p) and S equal to DualNumber(ZMod p). On A cubed,
use (x,y,z)(X,Y,Z)=(x+X,y+Y,z+Z+xY). Commutation is equality xY=Xy.
Normalize vectors into the disjoint charts (u,ut), (us,u) with s in the
maximal ideal, and pairs in that ideal. Fine slopes decide incidence within
a primitive chart; residue directions decide incidence with the third
chart. The two rings have the same residue coordinates and the same
normalized relation. A separate coefficient bijection transports z.

In both groups the derived subgroup is the z-axis. The integer-residue
axis contains an element whose p-th power is nonidentity. Every dual-number
axis element has p-th power equal to identity. Thus their derived groups
cannot be isomorphic. The proof uses no division by two.

## Falsifier

Any missing pair type, omission of central vertices, replacement of whole
triple distinctness by base distinctness, prime restriction, cardinality
mismatch or incorrect commutator convention would invalidate the claimed
source correspondence.

## Evidence

The native declaration is
`D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4.result`.
`ExactEvent` quantifies all natural primes and two actual finite group
bundles. Its conjunction contains both orders, a full simple-graph
isomorphism and negated source isoclinism. The Blueprint gives the exact
statement and coefficient correspondence. The generic Heisenberg subset is
attributed to Tau Ceti in the literature note and source header.

The exact-event registration is retained in its Reg mirror. The remaining
helper audit template boundaries are tracked in
[issue 29185](https://github.com/the-omega-institute/trureturing/issues/29185);
those audits are incomplete and do not substitute for independent review.

## Triage

### What the settlement shows

The compiled theorem gives an affirmative answer to the second sentence of
Q4, uniformly including the prime two. Its mechanism separates fine slope,
residue direction and central-coordinate multiplicity. The derived-group
obstruction concerns the same constructed pair. These assertions are
proved by the native theorem, rather than inferred from a finite sample.

The first sentence asks for a broader description of pairs with isomorphic
commuting graphs and remains outside this conclusion. No minimal-order,
uniqueness, full-centre classification or classification of isoclinism
classes is asserted. Other results of the article are not changed.
Final independent review, ordinary required checks and merge remain pending.

## ASSUMED-UNVERIFIED

Worldwide priority, exhaustive literature coverage and present-open
persistence beyond the inspected bounded sources are unverified. The
source's already known finite-prime cases and the generic API port are not
counted as new problem resolutions.
