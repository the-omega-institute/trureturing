---
slug: gonzalez-dleon-wachs-conjecture-4-13-2-refutation
bibkey: gonzalezdeleonwachs2026weighted
doi: 10.48550/arXiv.2608.08692
url: https://arxiv.org/html/2608.08692v1#S4.Thmtheorem13
triage: theorem
motivation_gids:
  - D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation
---

# Refutation of Gonzalez D'Leon-Wachs Conjecture 4.13(2)

## Problem

Conjecture 4.13(2) of arXiv:2608.08692v1 states that if `G` is a graph on
`n` vertices with `k` connected components and `H` is a spanning subgraph
with the same `k` components, then
`(-1)^(n-k) (mu_G - mu_H)` is real-rooted. Here `mu_G` is the Section 2
weighted bond-poset Mobius polynomial. The statement permits disconnected
graphs. This dossier concerns only part (2) as written.

## Motivation

The conjecture gives a root-location prediction for differences of the
weighted bond-poset polynomials introduced in the paper. A source-faithful
counterexample must retain connected blocks, admissible block weights, the
weighted refinement order, maximality, the singleton bottom, and the actual
incidence-algebra Mobius values; a supplied polynomial alone is insufficient.

## Gap

The bounded status check recorded in issue 8501 found no full proof or
refutation. arXiv:2609.15784v1 contains nestohedron recurrences but no located
resolution of Conjecture 4.13(2), and describes its Mobius-polynomial follow-up
as in preparation. These readings do not establish exhaustive literature
coverage or publication priority.

## Route

Take the vertex set `Fin 3 x Fin 3`. Let `G` be the union of three triangle
fibers and `H` the union of the corresponding three path fibers. Then `H < G`,
both graphs have nine vertices and exactly three connected components, and the
sign is positive. The literal three-vertex source posets give
`A = 2 + 5X + 2X^2` and `B = 1 + 3X + X^2`. Restriction to fibers and gluing
are inverse order isomorphisms preserving bottom, maximality, total weight,
and incidence-algebra Mobius values, so the two source polynomials are `A^3`
and `B^3`.

Their difference is `(X+1)^2 Q`, where
`Q = 7X^4 + 37X^3 + 63X^2 + 37X + 7`. For real `x`,
`4Q(x) = (2A(x)+B(x))^2 + 3B(x)^2`. A real zero would force `A(x)=B(x)=0`;
since `A-2B=-X`, this forces `x=0`, contradicting `B(0)=1`. Thus `Q` has no
real root and the difference does not split over the reals.

## Falsifier

A proof that the final polynomial splits over the reals, or that either graph
fails the literal hypotheses, would falsify this resolution. The kernel-checked
result proves the opposite using the exact source carrier and order rather than
an auxiliary recurrence.

## Evidence

- Source semantics:
  `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource.lean`.
- Three-vertex incidence-algebra computations:
  `D5/S0/Certificates/GonzalezDLeonWachsThreeVertexMobius.lean`.
- Product bridge, graph hypotheses, nonsplitting proof, and
  `result : Not claim`:
  `D5/S0/Certificates/GonzalezDLeonWachsWeightedBondDifferenceRefutation.lean`.
- The canonical split-module build and Lean report completed successfully; the
  three modules use only `propext`, `Classical.choice`, and `Quot.sound`.
- The source HTML was checked at SHA-256
  `1781237e65346eab7d5119fcf67abb2d795c505d7e99a26e572df891a760773e`.

The earlier monolithic compilation is not delivery evidence for the split
artifact. The canonical state pins and accepted events were produced by
`deposit-uncovered` against protected base
`3f8015a83dedcc59fe499fc5a16c08830997b8a8`.

## Triage

`theorem`. The explicit nine-vertex pair refutes Conjecture 4.13(2) in its
published all-graphs form. It does not refute part (1), and it does not settle
any connected-only variant obtained by adding a hypothesis absent from the
source statement.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The status check was bounded
to the recorded source and related searches, so no worldwide priority claim is
made. Source-to-Lean fidelity remains a review obligation outside the kernel:
the formal definitions and bridges are present and machine checked, while the
claim that they exactly transcribe the paper's prose requires independent
comparison with the cited version.
