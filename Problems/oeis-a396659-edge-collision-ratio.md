---
slug: oeis-a396659-edge-collision-ratio
bibkey: dutta2026a396659
doi: null
url: https://oeis.org/A396659/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Walks/CollisionPrefix
---

# The A396659 universal edge-collision ratio

## Problem

For every n at least two and every fixed starting vertex v on the complete
directed graph on n labeled vertices, including loops, count length-k walks
that visit every vertex, have distinct first k-1 directed edges, and repeat
one of these edges at the final step. With T(n,k) denoting this count, prove
or refute

$$\frac{T(n,n^2)}{T(n,n^2+1)}=\frac{2n-1}{n}.$$

The denominator must be positive. The sequences retain a distinguished start
and are not identified under rotation. The source is OEIS A396659 revision 16.

## Motivation

At either of these two lengths the distinct prefix uses all directed edges
or all but one. This reduces the required comparison to ordered Euler walks
and the location of one missing directed edge.

## Gap

The count and positive-denominator gaps are closed by the retained frozen result.

CollisionPrefix.short_count gives T(n,n*n)=(2*n-1)E and long_count gives
T(n,n*n+1)=nE on the source's literal ordered-edge carriers.
euler_nonempty constructs an Euler walk for each fixed start;
long_count_positive proves the denominator positive, and collision_ratio
states the exact rational identity for every n at least two.

Canonical freeze is retained. Current source/form and retained-Reg validation,
independent delivery review, required CI and merged delivery to dev remain
unfinished. All eight public-theorem escape audits remain unfinished under the
[linked-issue exception](https://github.com/the-omega-institute/trureturing/issues/24056#issuecomment-6516551237).
No delivered external-resolution count is asserted here.

## Route

Write E for the full Euler-walk count. Deleting the final repeated edge gives
T(n,n*n+1)=nE. An almost-complete trail omits either an edge from its endpoint
back to its start, or a loop at a different vertex while remaining closed.
Appending the omitted closing edge bijects the first class with Euler walks;
its final collision step has n-1 choices, giving (n-1)E.

For a different from v, let L(a) count trails missing only (a,a). Deleting that
loop from an Euler walk retains its insertion cut. The inverse inserts the
loop at the marked linear position. These cuts biject with the n-1 remaining
outgoing edges from a; neither boundary cut is at a. Thus E=(n-1)L(a).
Summing over the n-1 choices of a and cancelling n-1 gives the sum of L(a)
equal to E. These trails have n final choices, giving the numerator
(n-1)E+nE=(2n-1)E.

Euler existence uses a finite trail extension. Reserve each edge (a,v) until
all other outgoing edges from a have occurred. If an endpoint has no unused
outgoing edge, incidence balance forces it to be v. All edges entering v
then have occurred, so the reserved-exit invariant forces all directed edges
to have occurred. A shorter trail can therefore always extend, producing
exactly n*n distinct edges. This proves positivity without a count formula.

## Falsifier

Any n at least two and fixed start for which the literal finite counts violate
the ratio, or for which the denominator vanishes, refutes the whole statement.
A collision of two insertion positions would refute that proposed bijection,
without by itself refuting the ratio.

## Evidence

CollisionPrefix.sourceCollisionEquiv transports the distinguished start,
adjacency, vertex coverage and collision conditions between vertex walks
and the literal ordered-edge source carrier. longCollisionEquiv supplies
the denominator bijection. loopInsertionEquiv retains the marked insertion
cut; returnTrailEquiv completes the closing-edge class. short_count takes
cardinalities of their actual carriers. euler_nonempty uses the reserved-exit
construction; long_count_positive and collision_ratio give the two terminal
source obligations.

## Triage

The statement covers all n at least two, not a finite prefix. The separate
factorial formula is not assumed. No worldwide openness, priority, novelty or
model-diversity claim follows. The mathematical result is proved and frozen;
the delivery obligations and unfinished audits are stated above. No successor
problem is selected.

## ASSUMED-UNVERIFIED

Worldwide openness, priority, novelty and model diversity are unverified.
No current compile, required-CI success or merged delivery is asserted here.
The linked-issue exception does not complete any of the eight escape audits.
