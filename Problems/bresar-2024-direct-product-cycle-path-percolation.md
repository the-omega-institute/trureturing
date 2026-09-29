---
slug: bresar-2024-direct-product-cycle-path-percolation
bibkey: bresar2024bootstrapdirect
doi: 10.7151/dmgt.2603
url: https://arxiv.org/abs/2403.10957v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.result
---

# Problem 5 of Brešar, Hedžet and Herrman: m(C_n × P_m, 2)

## Problem

In `r`-neighbour bootstrap percolation a vertex becomes infected once it has
at least `r` infected neighbours, and `m(G, r)` is the least size of a nonempty
initial set that eventually infects every vertex. For the direct product
`C_n × P_m` of a cycle and a path, Brešar, Hedžet and Herrman
(arXiv:2403.10957, Discuss. Math. Graph Theory 46 (2026)) ask:

> Problem 5. Determine m(C_n × P_m, 2).

Their Proposition 3 gives `m(C_n × P_m, 2) ≤ n`, and they note that equality
appears to hold for small examples.

## Motivation

`D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.result`
proves `m(C_n × P_m, 2) = n` for every `n ≥ 3` and `m ≥ 1`.

## Gap

Issue #10650 preregisters the readings, the proof route and the literature
check. arXiv searches for bootstrap percolation and hull numbers on direct
products return only the source paper and unrelated models, and the citing
works found concern other graph families; the repository and pinned Mathlib
have no bootstrap percolation. `not-found-in-searched-scope`.

## Route

1. The layer `{(a, 0)}` percolates: `(a, b + 1)` has the two distinct
   neighbours `(a ± 1, b)` in layer `b`.
2. With `D(A) = Σ_{v ∈ A} |N(v) ∩ A|`, one round adds a set `B` disjoint from
   `A` whose vertices each have at least 2 neighbours in `A`; double counting
   the adjacent pairs between `A` and `B` gives `D(A ∪ B) ≥ D(A) + 4|B|`, so
   `4|A| − D(A)` never increases.
3. On the whole vertex set, `deg(a, b) = 2 deg_{P_m}(b)` and
   `Σ_b deg_{P_m}(b) = 2(m − 1)`, so `4|V| − D(V) = 4n`; a percolating set
   `A` satisfies `4n ≤ 4|A| − D(A) ≤ 4|A|`.

## Falsifier

The proof would fail if some round increased the potential of step 2, or if a
set of fewer than `n` vertices percolated.

## Evidence

Exhaustive search over all vertex subsets gives `m(C_n × P_m, 2) = n` for
`n = 3, …, 6`, `m = 1, …, 4` (`nm ≤ 20`), and the layer `{(a, 0)}` percolates for
`3 ≤ n, m ≤ 15`; the same search reproduces the paper's values
`m(P_3 × P_4, 2) = 6` and `m(P_4 × P_4, 2) = 8` (issue #10650).

The canonical source is
`D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.lean`.
Its public declarations are `dirProd`, `step`, `Percolates`,
`percolationNumber`, `claim` and `result`, with decidability instances for the
direct product and the path graph. The frozen module state has statement
identity
`sha256:69d8f41abf99c351717ab3929380eec70a7a5d0805c4d6533a62b37ee8bea65f`.
The result declaration has statement identity
`sha256:66586e9d4df394e6f9789928ecbb3695154b9c7a20a4c55bc8dd3cdf247908e4`.
The Freeze event is
`sha256:84f19ee39d98dd6ac7ee9e9fa4d3a75047d093bf913158cb69c40d41e9a5bf4a`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named open problem, preregistered in issue #10650 before the
probe. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the monotonicity of the potential under a round of
percolation and its value `4n` on `C_n × P_m` are new propositions on the live
proof path. Its admission basis is `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
