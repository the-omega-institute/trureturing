---
slug: espinosa-garcia-2026-hiv-wheel-extinction-refutation
bibkey: espinosagarcia2026hivwheels
doi: 10.48550/arXiv.2608.00340
url: https://arxiv.org/abs/2608.00340v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/WheelHivExtinctionRefutation.result
---

# The extinction set of the wheel W_18 contains 4

## Problem

Espinosa-García, Figueroa, Fresán-Figueroa, Maldonado and Sánchez-Solís
(arXiv:2608.00340v1) study Mukwembi's graph model of HIV infection. States
give each vertex the value `0` (healthy), `1` (infected) or `2` (dead). With
`d_{t,I}(v)` the number of infected neighbours of `v` and a positive
replacement parameter `R`, a healthy vertex becomes infected when
`d_{t,I}(v) ≥ 1`, an infected vertex dies, and a dead vertex is replaced by an
infected one when `d_{t,I}(v) ≥ R` and by a healthy one otherwise. The
extinction set `𝓔(G)` consists of the `R` for which every admissible initial
state (values in `{0, 1}`) reaches the all-healthy state. Conjecture 1 states:

> The extinction sets of the wheel graphs satisfy $\mathcal{E}(W_n) = \{3\}\cup\{R\in\mathbb{Z^+}:R\geq n-1\}$ for every even $n\geq12$, and $\mathcal{E}(W_n) = \{4\}\cup\{R\in\mathbb{Z^+}:R\geq n-1\}$ for every odd $n\geq17$.

Issue #10263 fixes the reading: `W_n = K₁ ∨ C_{n−1}` on `Fin n` with hub `0`
and the cycle `1, 2, …, n − 1`, and `𝓔(W_n)` as defined, quantified over all
`2^n` admissible initial states.

## Motivation

The paper's table of extinction sets for `11 ≤ n ≤ 26` is described there as
experimental evidence rather than an exhaustive determination.
`D5/S3/Combinatorics/WheelHivExtinctionRefutation.result` shows by an
exhaustive kernel-checked computation that `4 ∈ 𝓔(W_18)`, which contradicts
the even case of the conjecture at `n = 18`.

## Gap

Issue #10263 preregisters the refutation and its literature check. arXiv
lists only version 1 (2026-07-31); Semantic Scholar reports no citing paper.
These readings are `not-found-in-searched-scope`.

## Route

All `2^18` admissible initial states of `W_18` are simulated at once. For each
vertex a natural number records in bit `j` whether the vertex is infected in
the state reached from the `j`-th initial state, whose vertex `v` is infected
exactly when bit `v` of `j` is set; a second number records the dead
vertices. The initial masks are built by repeated doubling of a block of
bits, and bit `j` of the mask of vertex `v` equals bit `v` of `j`. One step of
the rules becomes bitwise `and`, `or` and `xor`; for each vertex, masks for
"at least `k` of the neighbours are infected" are computed bit by bit from the
neighbours' masks. At every bit, the masks after one step describe one step
of the rules applied to the state described before, so by induction the masks
after `t` steps describe the `t`-th state of every initial state. The kernel
evaluates the masks after `25` steps and finds them all zero; hence every
admissible initial state reaches the all-healthy state by time `25` when
`R = 4`, so `4 ∈ 𝓔(W_18)`, while `4 ∉ {3} ∪ {R ≥ 17}`.

## Falsifier

The refutation would fail if some admissible initial state of `W_18` with
`R = 4` never reached the all-healthy state.

## Evidence

An independent bit-sliced simulation in Python finds all `262144` initial
states of `W_18` extinct at `t = 25` with `R = 4`, and `51` of them still alive
at `t = 24`. As positive controls, the same simulation keeps initial states
alive after `200` steps for `W_16` with `R = 4` (the paper's table has
`4 ∉ 𝓔(W_16)`), `W_18` with `R = 5` and `W_12` with `R = 4`. The values
`R ≤ n` for which every initial state reaches the all-healthy state within
400 steps are `{3, 11, 12}`, `{12, 13}`, `{3, 13, 14}`, `{14, 15}`,
`{3, 15, 16}`, `{4, 16, 17}`, `{3, 4, 17, 18}`, `{4, 18, 19}`, `{3, 4, 19, 20}`
for `n = 12, …, 20`. Each listed value belongs to `𝓔(W_n)`; a value not
listed only failed to clear every initial state within 400 steps, which is
not a proof that it lies outside `𝓔(W_n)`. The listed values match the
paper's table up to `n = 17`; at `n = 18` and `n = 20` the value `4` is listed
while the table omits it.

The canonical source is
`D5/S3/Combinatorics/WheelHivExtinctionRefutation.lean`. Its public
declarations are `wheelAdj` with its decidability instance, `infectedCount`,
`step`, `extinctionSet`, `claim`, and `result`; the bit-sliced simulation uses
private non-proposition definitions, and the code of an initial state is the
frozen `bitsValue` of `D5/S0/Computability/PhysicalDivider/WordArithmetic`.
The frozen module state has statement
identity
`sha256:4bf1e1451030dbb0a28c71ac467e22252abc0a60423bff418be726b518a6d24b`.
The result declaration has statement identity
`sha256:5addb16fd800bbb6df4449cbc2daca34dee660cdad13ca20d32ed9a5379a0cf8`.
The Freeze event is
`sha256:c1a4e4806b4412c108ac803e4f5f41ed7c3d410028dc67e55e20e6d27ef64ae5`
and its project-level frozen prerequisite is
`D5/S0/Computability/PhysicalDivider/WordArithmetic`. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #10263 before the
probe. `theorem` (a refutation); resolution `refuted`. Utility
`kind=certified-instance; basis=refutes`, with typed `claim` and `result`.
The public theorem has `proof_shape: content`: the correspondence between the
masks and the rules at every bit, and the counting masks, are new propositions
on the live proof path. Its admission basis is `open-problem-resolution`.

## ASSUMED-UNVERIFIED

The odd case of the conjecture, which the Python simulation contradicts at
`n = 23` (`5 ∈ 𝓔(W_23)`), is not formalized here. The bounded literature
check does not establish exhaustive worldwide novelty, priority, or the
absence of an independent proof.
