---
slug: chervov-2026-cayleypy4-three-cycle-grassmannian-diameter
bibkey: chervov2026cayleypy4
doi: 10.48550/arXiv.2603.22195
url: https://arxiv.org/abs/2603.22195v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.result
---

# The diameter of the inverse-closed consecutive 3-cycle Schreier coset graph

## Problem

CayleyPy-4 (arXiv:2603.22195v1) studies the Schreier coset graph
`S_N / (S_L × S_{N−L})` whose vertices are the binary words with `L` zeros and
`N − L` ones and whose generators are the consecutive `k`-cycles
`(i, i + 1, …, i + k − 1)`, `0 ≤ i ≤ N − k`, for `N > k`. In the
inverse-closed case a move rotates `k` consecutive letters one place in either
direction. The `k = 3` clause of Conjecture 16 states:

> For $k=3$ from $L\ge 2$(?): $D(L, N) = \left\lceil \frac{L (N - L)}{2} \right\rceil$

Issue #10230 fixes the readings: words are `List Bool` with `false` for `0`;
"diameter" is read both as CayleyPy computes it, the largest distance from the
central state `[0]^L + [1]^{N−L}`, and as the largest distance between two
vertices; the range is `2 ≤ L ≤ N` and `N > 3`.

## Motivation

The paper proposes these diameters as bivariate quasipolynomials in `N` and
`N − L`, with leading term `L(N − L)/(k − 1)`. The frozen declaration
`D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.result` proves the
`k = 3` clause under both readings.

## Gap

Issue #10230 preregisters the clause and its literature check. arXiv lists
only version 1 (2026-03-23). Semantic Scholar reports two citing papers,
arXiv:2607.13219 (an R package for the TopSpin puzzle) and arXiv:2607.12026 (a
census of Cayley graphs of small groups); neither abstract concerns these
coset graphs. Web searches for the formula and for sorting binary strings by
rotations of three consecutive letters found no statement of it; the
short block-move model also allows adjacent swaps and is a different graph.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

Let `M = N − L` and let `f(L, M) = ⌈LM/2⌉`.

- Lower bound. The inversion count of a word is the number of positions
  `p < q` holding a one at `p` and a zero at `q`. By the frozen
  `D5/S1/Digit/Carry/ListInversions.inv_window`, rotating three consecutive
  letters changes only the inversions inside the window, so one move changes
  the count by at most `2`. The central state has no inversion and its
  reversal `1^M 0^L` has `LM`, so reaching the reversal from the central state
  takes at least `f(L, M)` moves.
- Upper bound, from any vertex `x` to any vertex `y`, by induction on `N`. For
  `N = 3` the three arrangements with the same letters are pairwise one move
  apart. For `N ≥ 4` let `b` be the last letter of `y` and `ρ` the number of
  letters after the last `b` in `x`. The move `b c c ↦ c c b` carries `b` two
  places to the right, and when `ρ` is odd a final move `a b c ↦ c a b` ends
  the word with `b`; this costs `⌈ρ/2⌉` moves, and the first `N − 1` letters
  are handled by induction.
- Budget. For `b = 1`, `ρ ≤ L` and the budget is
  `f(L, M) − f(L, M − 1)`, which is `L/2`, `(L + 1)/2` or `(L − 1)/2` as `L` is
  even, `L` and `M` are odd, or `L` is odd and `M` even; it fails only when `L`
  is odd, `M` is even and `ρ = L`. For `b = 0` it fails only when `M` is odd,
  `L` is even and `ρ = M`. In these two cases `x` ends in the other letter, so
  the same peeling from `y` towards `x` is within its budget, and since every
  move has an inverse move, a path from `y` to `x` gives one from `x` to `y`.

## Falsifier

The clause would fail if some pair of vertices were more than `⌈LM/2⌉` moves
apart, or if the central state reached every vertex in fewer. The floor
variant `⌊LM/2⌋` already fails at `L = 3`, `N = 4` (eccentricity `2`).

## Evidence

Exact breadth-first search for `4 ≤ N ≤ 11` and `2 ≤ L < N` (44 pairs) gives
central eccentricity and all-pairs diameter both equal to `⌈L(N − L)/2⌉`;
with the floor variant as positive control, 6 pairs with `N ≤ 9` disagree. The
peeling construction with the parity choice was run on every ordered pair of
vertices for `3 ≤ N ≤ 9` (66 188 pairs) and never exceeded `⌈L(N − L)/2⌉`
moves; always peeling from `x`, without the parity choice, exceeds it in 70
cases.

The canonical source is
`D5/S3/Combinatorics/ShrunkenGrassmannianThreeCycleDiameter.lean`. Its public
declarations are `rotL`, `rotR`, `Step`, `Reach`, `IsVertex`, `ecc`, `diam`,
`claim`, and `result`; the central state is `normalWord L (N − L)` from
`D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange`. The frozen module state has statement identity
`sha256:8a4a2bfc4fac0ced0b8b5b4196cbc04a84d4df04947703f8e9c5c16203a138ae`.
The result declaration has statement identity
`sha256:b6b74d024706e5795cb0c028530f1bfa21ce010dbb32e3596f847fd0fc9b8a97`.
The Freeze event is
`sha256:40eeefbcdd042b163fa1c4ea7f494f1b898e0b1e4aaeaef114a2e008b3a6d9b1`.
Its project-level frozen prerequisites are
`D5/S1/Digit/Carry/ListInversions` and
`D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange`. The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`,
or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10230 before the
probe. `theorem`; resolution `proved` for the `k = 3` clause of Conjecture 16.
The public theorem has `proof_shape: content`: the peeling lemma, the parity
budget, the symmetry of reachability and the inversion-potential bound are new
propositions on the live proof path, not instances of pinned or frozen
statements. Its escape witness is form (2), the public conclusion itself, and
its admission basis is `open-problem-resolution`. Utility `none`: it is a
theorem for every `L` and `N`.

## ASSUMED-UNVERIFIED

The `k = 4` and `k = 5` clauses of Conjecture 16 are not settled here. The
bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The Lean kernel does not
authenticate the external source or its version history.
