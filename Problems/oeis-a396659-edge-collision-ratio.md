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

The whole ratio is unresolved here. Required further results are the
cardinality decomposition of the numerator, the loop-deletion/insertion
bijection with marked departures, and existence of a full ordered Euler walk
for every n and fixed start. The denominator factor alone does not settle
the ratio.

## Route

Write E for the full Euler-walk count. Deleting the final repeated edge gives
T(n,n^2+1)=nE. An almost-complete trail omits either an edge from its endpoint
back to its start, or a loop at a different vertex while remaining closed.
The former class should contribute (n-1)E. For each other vertex a, let L(a)
count full trails missing only its loop. The remaining desired correspondence
is E=(n-1)L(a), obtained by deleting that loop while marking its insertion
cut. Summing over the n-1 choices of a then gives the required numerator.
These cardinality statements must be proved for the same ordered carriers.

## Falsifier

Any n at least two and fixed start for which the literal finite counts violate
the ratio, or for which the denominator vanishes, refutes the whole statement.
A collision of two insertion positions would refute that proposed bijection,
without by itself refuting the ratio.

## Evidence

CollisionPrefix defines the source's ordered edge sequences and compatible
vertex walks, together with their exact collision correspondence. Its
prefix_structure and collision_prefix_structure describe the two omitted-edge
cases and the automatic coverage of vertices. Its longCollisionEquiv is the
append/delete construction underlying long_count. These statements leave the
numerator and positivity obligations above.

## Triage

This is an all-n finite combinatorial problem. No finite prefix, factorial
formula assumed from the source, or assertion of global novelty supplies a
resolution. The next mathematical target is the loop-insertion equivalence
with a count of its distinct ordered cuts. No successor problem is selected.

## ASSUMED-UNVERIFIED

The proposed numerator and positive-denominator arguments have not been
established by the declarations listed above. The current source's conjecture
label is source evidence, not a proof of worldwide nonsettlement.
