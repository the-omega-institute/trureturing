---
slug: kok-jaco-dom-path-diameter-refutation
bibkey: kok2025jaco
doi: 10.48550/arXiv.2507.16500
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.result
---

# Refutation of Kok's dom-path diameter conjecture

## Problem

Kok, arXiv:2507.16500v1, Observation 2.7 and Conjecture 2.9 on printed
pages 6--7, defines a primary minimal dom-path by a shared gamma-set and
states:

> For any linear Jaco graph Jn (x), n >= 1 the length of a diam-path and a
> primary minimal dom-path Pd satisfy |Pd| - |diam(Jn (x))| <= 1.

The paper measures path length in edges. The formal target is the weakest
selection-independent consequence: for every positive `n`, some dom-path has
edge length at most the Mathlib diameter of `J_n(x)` plus one. Refuting this
existential consequence refutes every possible choice of primary minimal
dom-path satisfying the source's defining property.

## Motivation

The paper presents Conjecture 2.9 as an open bound and leaves its conjectures
for future work. A finite Jaco graph in which every dom-path exceeds the
diameter by at least two settles the stated inequality without requiring a
unique formalization of the source's primary-path selection rule.

## Gap

The arXiv API and searches for `"Jaco" "Conjecture 2.9"`, `"Jaco"
"dom-path"`, `"linear Jaco graphs" conjecture proof`, and `"linear Jaco
graphs" 33 domination` were checked on 2026-09-18. No proof, refutation,
correction, later arXiv version, journal reference, or DOI beyond the arXiv
DOI was found in those checked surfaces. Semantic Scholar returned HTTP 429,
Google Scholar was not checked, and the full text of Kok's cited domination
research note was not available. This is a bounded search report and makes no
claim of exhaustive coverage or first-publication priority.

## Route

Restrict the frozen infinite Jaco adjacency to vertices 1 through 33. A
finite neighborhood computation, justified by induction from membership in a
bounded neighborhood to a walk of bounded length, gives graph diameter at
most seven. Every dominating set of this graph has at least four vertices.

If a dom-path had at most eight edges, its path graph would have at most nine
vertices and domination number at most three. The shared set required by the
dom-path definition would then have both at least four and at most three
members, a contradiction. The explicit walk with vertices
`1,2,3,4,7,11,12,20,32,33` and shared dominating set `{2,7,20,33}` shows that
the dom-path predicate is inhabited.

## Falsifier

The counterexample is the finite linear Jaco graph at `n = 33`. A correction
showing that this graph has diameter at least eight, has a dominating set of
at most three vertices, or has a dom-path of at most eight edges would
invalidate the refutation. A mismatch between the encoded finite adjacency,
the shared gamma-set condition, and the source definitions would invalidate
the source-level interpretation.

## Evidence

- Lean module:
  `D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.lean`.
- Resolution theorem: `result : not claim`; the `Refuted` resolution claim is
  attached only to this theorem.
- The live structural step `exists_walk_of_mem_within` turns bounded-neighborhood
  membership into a walk of bounded length and supplies the diameter estimate.
- The explicit ten-vertex walk and the set `{2,7,20,33}` witness that
  `IsDomPath 33` is inhabited.
- Axiom closure for `result`: `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The universal conjecture is refuted by the certified instance at
`n = 33`.

## ASSUMED-UNVERIFIED

The identification of the paper's finite linear Jaco graph and primary
minimal dom-path terminology with the encoded adjacency and shared minimum
dominating-set predicate rests on a source reading, not a kernel proof.
Literature coverage and publication priority are not kernel-checked; the
bounded searches listed above found no resolution in the checked surfaces.
