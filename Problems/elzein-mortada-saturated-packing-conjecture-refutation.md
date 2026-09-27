---
slug: elzein-mortada-saturated-packing-conjecture-refutation
bibkey: elzein2026local
doi: 10.48550/arXiv.2603.25113
url: https://arxiv.org/abs/2603.25113v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.result
---

# El Zein-Mortada Saturated Packing Refutation

## Problem

El Zein and Mortada, arXiv:2603.25113v1, Conjecture 3, printed page 27,
state: "Every 2-saturated subcubic graph is (1, 1, 2)-packing
colorable." A subcubic graph has maximum degree at most three. It is
2-saturated when each degree-three vertex has at most two degree-three
neighbors. A `(1,1,2)`-packing coloring partitions the vertices into two
independent classes and one class whose distinct vertices have distance
greater than two. The printed conjecture contains no local-girth hypothesis.

## Motivation

The frozen theorem
`D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.result`
settles the printed universal statement by an exact seven-vertex
counterexample. It separates the statement as printed from the preceding
discussion of local girth and makes no assertion about a strengthened
local-girth version.

## Gap

Issue 8799 records a bounded prior-resolution screen covering targeted arXiv
and repository searches. It found the source at version 1 and a later paper
resolving other conjectures from the same article, but no resolution of
Conjecture 3 in the searched scope. The arXiv record lists only version 1.
Google Scholar and exhaustive non-arXiv literature coverage are unverified.

## Route

Use the connected graph with graph6 encoding `FhcYG`, vertices 0 through 6,
and edges 01, 04, 12, 16, 23, 34, 35, 45, and 56. Its degree sequence is
`[2,3,2,3,3,3,2]`; its four degree-three vertices have respectively 0, 2, 2,
and 2 degree-three neighbors, so the graph is subcubic and 2-saturated.

The triangle on vertices 3, 4, and 5 forces one of those vertices into the
radius-two class. Every graph vertex is within distance two of each triangle
vertex, so no other vertex can use that class. Deleting vertex 3, 4, or 5
leaves respectively the five-cycle 0-1-6-5-4-0, 1-2-3-5-6-1, or
0-1-2-3-4-0. The remaining vertices cannot be divided between the two
independent classes.

## Falsifier

An omitted edge, an incorrect degree or saturation computation, a vertex more
than distance two from a triangle vertex, or a two-coloring of one of the
listed five-cycles would invalidate the counterexample. A source restriction
on local girth would define a different claim from the printed Conjecture 3:
under the paper's prose reading of `g₃` (every degree-3 vertex has local girth
at least four) this graph is excluded, since its degree-3 vertices have local
girths 5, 3, 3, 3; under the paper's displayed formula `g₃(G) = max{g(v) :
d_G(v) = 3}` it has `g₃ = 5` and is not excluded.

## Evidence

The formal module defines the source predicates `Subcubic`, `Saturated`, and
`IsPacking112`, the closed proposition `claim`, and the sole public theorem
`result : Not claim`. The proof checks the graph hypotheses by kernel
evaluation, derives the distance bounds from explicit walks, and exhausts the
remaining finite color cases. Its Scribe theorem node binds the frozen result
to this dossier with `OpenProblemResolutionClaim(Refuted)`.

## Triage

`theorem`; Tier 1 recent named external conjecture, preregistered in issue
8799 before the proof probe. The admission basis is
`open-problem-resolution`; the conservative classification is
`proof_shape: bind-only` with `escape_witness: none`. The computational use is
a `certified-instance` with a typed `refutes` edge from `result` to `claim`.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded screen cannot
exclude every prior resolution or establish publication priority.
Source-to-Lean fidelity requires independent comparison with
arXiv:2603.25113v1; the Lean kernel checks the formal statement and proof, not
that prose correspondence. The typed resolution binding does not itself
establish repository merge or external publication.
