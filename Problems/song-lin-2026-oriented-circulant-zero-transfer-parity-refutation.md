---
slug: song-lin-2026-oriented-circulant-zero-transfer-parity-refutation
bibkey: song2026zerotransfer
doi: 10.48550/arXiv.2608.10643
url: https://arxiv.org/abs/2608.10643v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result
---

# Song and Lin's parity conjecture for zero transfer on oriented circulant graphs

## Problem

Song and Lin study the continuous-time quantum walk `U(t) = exp(-i t H)` on a
mixed graph, where the Hermitian adjacency matrix `H` has entry `i` on an arc
`u → v`, `-i` on the reversed arc and `0` elsewhere on an oriented graph. A
graph has zero transfer from `u` to `v` if `U(t)_{u,v} = 0` for every time
`t ≥ 0`. For the oriented circulant graphs `G(ℤ_n, C)`, with arcs `a → b` for
`b - a ∈ C`, `C ⊆ ℤ_n ∖ {0}`, `C ∩ -C = ∅`, and connectedness assumed
throughout the section, they state Conjecture 3.1 of arXiv:2608.10643v1:

> Let Γ = G(ℤ_n, C) be an oriented circulant graph with n ≡ 2 (mod 4). If
> zero transfer occurs between vertex v and 0, then v must be odd.

Issue #10142 fixes the readings: vertices are `ZMod n`; `U(t)` is the matrix
exponential of `-(i t) H`, taken as the frozen propagator
`hamiltonianPropagator H t = exp (t • (-i) • H)` of
`D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow`; zero transfer between `v` and `0` is read in both
directions at once, which only strengthens the hypothesis; connectedness is
that of the underlying undirected graph; "v is odd" means that the
representative of `v` in `0, …, n − 1` is odd.

## Motivation

Zero transfer models the isolation of a vertex from quantum state transfer.
The frozen declaration
`D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.result` proves that the
conjecture is false: on the connected oriented circulant graph
`G(ℤ_30, {5, 6, 9, 20})` there is zero transfer between `0` and the even
vertex `2`.

## Gap

Issue #10142 preregisters the conjecture and its literature check. arXiv
lists only version 1 (2026-08-11) and no journal reference. Semantic Scholar
reports no citing paper. The paper's own search covers `n ≤ 20`, and its
remark after the conjecture records that a general algebraic proof remains
open.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent refutation.

## Route

Write `H = i S`, where `S` is the integer skew-symmetric matrix with entry `1`
on arcs and `-1` on reversed arcs; then `H^k = i^k S^k`. The rows
`r_k = (S^k)(0, ·)` satisfy `r_{k+1} = r_k S`. Seven exact row products give
`r_1, …, r_7`, with `r_k(2) = 0` for `k ≤ 6` and

`r_7 = −32 r_5 − 320 r_3 − 960 r_1`.

Multiplying by `S^k` gives `r_{k+7} = −32 r_{k+5} − 320 r_{k+3} − 960 r_{k+1}`
for every `k`, so strong induction yields `(S^k)(0, 2) = 0` for all `k`.
Since `Sᵀ = −S`, `(S^k)(2, 0) = (−1)^k (S^k)(0, 2) = 0`. Every term of the
exponential series of `-(i t) H` then has vanishing `(0, 2)` and `(2, 0)`
entries, and so does `U(t)` for every real `t`. The set `C` is oriented, and
`a → a + 6 ← a + 1` joins each vertex to the next, so the graph is connected.

## Falsifier

The refutation would fail if the conjecture's zero transfer used a transition
matrix other than `exp(-i t H)` with this Hermitian adjacency matrix, or if
"odd" referred to something other than the residue class of `v` modulo the
even order `n`.

## Evidence

Exact integer computation gives `(S^k)(0, 2) = 0` for `k = 0, …, 89` and the
matrix identity `S^7 = −32 S^5 − 320 S^3 − 960 S`; the zero-transfer set of
`0` is `{1, 2, 4, 7, 8, 11, 13, 14, 16, 17, 19, 22, 23, 26, 28, 29}`, which
contains the even vertices `2, 4, 8, 14, 16, 22, 26, 28`. Numerically,
`max(|U(t)_{0,2}|, |U(t)_{2,0}|) ≤ 2.8 × 10^{-15}` at 201 sampled times in
`[0, 20]`. As a positive control, the same computation reproduces the
paper's order-21 example, where `C = {2, 10, 12, 15, 16, 17}` has zero
transfer from `0` exactly at `7` and `14`.

The canonical source is
`D5/S3/Quantum/Dynamics/OrientedCirculantZeroTransfer.lean`. Its public
declarations are `hermAdj`, `ZeroTransfer`, `Oriented`, `Connected`, `claim`,
and `result`. The frozen module state has statement
identity
`sha256:b2413157cffdbf007294c0de4cc3c07e53b6481a3d313928f43783a244b08f60`.
The result declaration has statement identity
`sha256:e4bd9bb53145e48ce490502c2175c76ada22eecee75a4091285b1e585a447c5b`.
The Freeze event is
`sha256:38759c7d2112465fd527290d5563153eae6dda19b82a3ec94e2f6e1c5315c897`
and has one project-level frozen prerequisite, the module
`D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow` (statement identity
`sha256:ac6db85112e8f370397968c1e3e9584b6b0cf72c9768661d36f565e28d242cd8`),
whose `hamiltonianPropagator` and `hamiltonianGenerator` the definitions and
the proof use. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10142 before the
probe. `theorem`; resolution `refuted`. The public theorem has
`proof_shape: content`: the vanishing of the `(0, 2)` and `(2, 0)` entries of
every power of `S` is an infinite family obtained from the degree-seven row
recurrence and strong induction, not an instance of pinned lemmas. Its
escape witness is form (2), the public conclusion itself, and its admission
basis is `open-problem-resolution`. Its computational use is a
`certified-instance` with `basis=refutes`: the result negates the closed
claim.

## ASSUMED-UNVERIFIED

The minimality of `n = 30` among orders `n ≡ 2 (mod 4)` and the count of
failing connection sets at `n = 30` were reported by a search agent and not
rerun; the formal statement depends only on the single witness. The bounded
literature check does not establish exhaustive worldwide novelty, priority,
or the absence of an independent refutation. The Lean kernel does not
authenticate the external source or its version history.
