---
slug: akbari-elahimanesh-miraftab-windmill-factorization
bibkey: akbari2025primematrixproduct
doi: 10.48550/arXiv.2512.24864
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.result
url: https://arxiv.org/html/2512.24864v1#S5
---

# Windmill adjacency-matrix factorization

## Problem

Akbari, Elahimanesh and Miraftab ask in Section 5, item 1 of *On Prime Matrix Product Factorizations* to determine all pairs $(d,t)$ for which the windmill $W_{d,t}$ admits a factorization. Here $d\ge1$, $t\ge3$, and the hub is the common vertex of the $d$ copies of $K_t$. [Published question](https://arxiv.org/html/2512.24864v1#S5.I1.i1)

> We ask to determine all pairs $(d,t)$ for which $W_{d,t}$ admits a factorization.

### Statement echo

The windmill admits a factorization if and only if $d=1$ and $t\equiv1\pmod4$.

| Source clause | Lean counterpart |
| --- | --- |
| All $d\ge1$ and $t\ge3$ | Natural parameters `d t` with hypotheses `1 ≤ d` and `3 ≤ t`. |
| One shared hub and $d$ labelled blades of order $t$ | `Option (Fin d × Fin (t - 1))` and the adjacency relation of `windmill d t`. |
| Ordinary adjacency-matrix factorization | An existential pair of `SimpleGraph` factors on that carrier and equality of their ordinary integer `adjMatrix` product with the windmill matrix. |
| The complete set of admissible pairs | `result` proves the equivalence with `d = 1 ∧ t % 4 = 1`. |

## Motivation

This problem asks for the full classification of ordinary adjacency-matrix products on windmills. The graph has a single vertex shared by every blade, so a factorization must account for all hub entries and all cross-blade zero entries.

## Gap

The published question leaves the multiblade case to be classified. The single-blade case is covered by the complete-graph criterion.

## Route

Symmetry allows the two factors to be reversed. Commutation with the windmill adjacency matrix forces both factors to have a hub neighbor in each blade. Two different blades would then have a common intermediate vertex in the product, contrary to their prescribed zero entry.

A single blade is complete. The product of the two regular factor degrees is $t-1$. Each degree is even by the degree-sum formula on the opposite factor induced on a neighborhood. Conversely, two symmetric cyclic step sets give one two-step path for each nonzero difference and none for zero. This is the complete-graph criterion of Maghsoudi, Miraftab and Suda. [Theorem 1.2](https://arxiv.org/html/2312.08615v1#S1.Thmthm2)

## Falsifier

An admissible factorization with more than one blade or with a blade order outside residue class one modulo four would contradict necessity. An admissible one-blade order of residue one for which every factor pair fails would contradict sufficiency.

## Evidence

The classification and its earlier exact-statement Lean replay are credited to the settlement in [issue #34699](https://github.com/the-omega-institute/trureturing/issues/34699#issuecomment-7208053328).

The Lean declaration `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.result` gives the equivalence on the specified carrier for every admissible pair.

## Triage

- **Proved.** The windmill is factorable exactly when $d=1$ and $t\equiv1\pmod4$.

## ASSUMED-UNVERIFIED

Literature completeness and independent priority are unverified.
