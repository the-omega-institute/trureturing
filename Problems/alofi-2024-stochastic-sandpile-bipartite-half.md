---
slug: alofi-2024-stochastic-sandpile-bipartite-half
bibkey: alofi2024lackingbipartite
doi: 10.1016/j.disc.2024.114323
url: https://arxiv.org/abs/2411.02667v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.result
---

# Question 6 of Alofi and Dukes: do the stochastically recurrent states of K_{m,n} dominate?

## Problem

In the stochastic sandpile model of Chan, Marckert and Selig, a stable
configuration `c` on a graph with sink is stochastically recurrent when some
orientation `O` satisfies `in_O(v) ≥ d(v) − c(v)` at every non-sink vertex.
For the complete bipartite graph `K_{m,n}` with the sink in the first part,
Alofi and Dukes (arXiv:2411.02667, Discrete Math. 348 (2025) 114323) record
`n^{m−1} m^{n−1} ≤ |Sto(K_{m,n})| ≤ n^{m−1} m^n` and ask:

> Question 6. Can it be determined whether or not the number of stochastically
> recurrent states dominates the set of stable states? I.e. can it be decided
> |Sto(K_{m,n})| ≶ n^{m−1} m^n / 2 ?

## Motivation

`D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.result`
proves `2 |Sto(K_{m,n})| ≤ n^{m−1} m^n` for all `m ≥ 2`, `n ≥ 1`, with
equality if and only if `m = 2`: the stochastically recurrent states never
dominate.

## Gap

Issue #10704 preregisters the readings, the proof route and the literature
check. The paper itself characterises `Sto(K_{2,n})`, and Selig and Zhu
(arXiv:2409.11811) characterise the stochastically recurrent configurations of
`K_{m,n}`, but neither compares their number with half of the stable
configurations; the citing work found does not address the question.
`not-found-in-searched-scope`.

## Route

1. Every orientation directs each of the `mn` edges into exactly one vertex,
   so the in-degrees sum to `mn`; summing `in_O(v) + c(v) ≥ d(v)` over the
   non-sink vertices gives at least `2mn − n − mn = n(m − 1)` grains.
2. The involution `c(v) ↦ d(v) − 1 − c(v)` sends `S` grains to
   `(m − 1)(2n − 1) − S`, so it maps `{S ≥ n(m − 1)}` injectively into the
   disjoint set `{S ≤ (m − 1)(n − 1)}`.
3. For `m = 2` an explicit orientation makes every configuration with `n`
   grains recurrent, and the involution exchanges `{S ≥ n}` and
   `{S ≤ n − 1}`; for `m ≥ 3` a configuration with `n(m − 1) − 1` grains lies
   in neither set.

## Falsifier

The answer would fail if some recurrent configuration had fewer than
`n(m − 1)` grains, or if for `m ≥ 3` twice the number of recurrent states
reached the number of stable configurations.

## Evidence

Exhaustive computation over all orientations gives `|Sto| / stable` equal to
`1/2, 4/8, 12/24, 32/64` for `m = 2`, `n = 1, …, 4`, and `1/3, 13/36, 90/243,
486/1296, 1/4, 38/128, 537/1728` for `(m, n) = (3,1), (3,2), (3,3), (3,4),
(4,1), (4,2), (4,3)`; the same computation reproduces the paper's
`Sto(K_{2,2})` of Example 5 (issue #10704).

The canonical source is
`D5/S3/StatisticalMechanics/Sandpiles/StochasticSandpileBipartiteHalf.lean`.
Its public declarations are `IsOrientation`, `indeg`, `Stable`, `Sto`,
`claim` and `result`, with a decidability instance for the adjacency of
`completeBipartiteGraph`. The frozen module state has statement identity
`sha256:66f9ad3d071bc39d873b66cc43e41f00625debb75434a7432e49587ff0db6650`.
The result declaration has statement identity
`sha256:827b40093a749c2657980b8969d6ebec5300dd42054f7d2fe3de021f15f50ea4`.
The Freeze event is
`sha256:3585da88b101e48f3eafcc690d23e52d5324d800a13e4b0073dc1e484cceae7c`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named open problem, preregistered in issue #10704 before the
probe. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the lower bound on the grains of a recurrent
configuration and the involution count are new propositions on the live proof
path. Its admission basis is `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
