---
slug: haritha-chithra-2022-distance-seidel-energy-problem-5-1
bibkey: harithachithra2022distanceseidel
doi: 10.1080/09728600.2025.2479147
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.result
url: https://arxiv.org/abs/2210.05940v2
---

# Distance Seidel energy after deleting an edge

## Problem

T. Haritha and A. V. Chithra, *Distance Seidel matrix of a connected graph*, arXiv:2210.05940v2, page 13, Problem 5.1:

> Let G = K_{a,b}, with a, b > 1. Is E_{D^S}(K_{a,b} − e) > E_{D^S}(K_{a,b}), for any edge e of K_{a,b}?

The answer is affirmative for the source's matrix equation $D^S(G)=J-I-2D$, for every $a,b\ge2$ and every edge. The source's casewise expression instead gives diagonal one. The universal statement here concerns the zero-diagonal matrix equation; the diagonal-one alternative has only the finite evidence below.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $D^S(G)=J-I-2D$ | `distSeidel` | Literal entrywise expression with shortest-path distance and zero diagonal. |
| $E_{D^S}(G)=\sum_r|\partial_r^S|$ | `energy` | Absolute real characteristic roots, counted with multiplicity; the matrices used by the theorem are real symmetric. |
| $G=K_{a,b}$ | `completeBipartiteGraph (Fin a) (Fin b)` | Carrier `Fin a ⊕ Fin b`; graph constructions are Mathlib's. |
| $a,b>1$ | Both natural-number hypotheses in `claim` | Exactly $2\le a$ and $2\le b$. |
| Any edge $e$ | Universal quantifier over `edgeSet` in `claim` | Unordered edges; no particular edge is selected in the public conclusion. |
| Delete $e$ and increase energy strictly | `deleteEdges` and strict inequality in `claim`, proved by `result` | The singleton edge set is removed; all source clauses are retained. |
| Finite decidable vertex carrier | The instance parameters of `distSeidel` and `energy` | Supplies finite matrices and sums, without an additional graph restriction. |

## Motivation

The settling GID is `D5/S3/Combinatorics/Graph/KyFanGap/HarithaChithraDistanceSeidelEnergy.result`, preregistered in [#19532](https://github.com/the-omega-institute/trureturing/issues/19532). The source is recorded in `Library/GraphInvariants/harithachithra2022distanceseidel.md`. The source's Propositions 5.2–5.3 cover the first-part sizes two and three; the conclusion here covers the entire family.

## Gap

Problem 5.1 is settled under the displayed matrix equation. Literature completeness is `ASSUMED-UNVERIFIED`. No universal conclusion for $J-2D$, and no classification of other graphs or multiple-edge deletions, is asserted.

## Route

Write $M=D^S(K_{a,b})$ and $H=I-2P$, where $P$ projects onto the span of the two part indicators. The private declarations `Blocks.H_sq`, `Blocks.H_mul_M`, `Blocks.S_posSemidef` and `Spectral.sign_energy` establish the supporting trace identity. `baseline_energy` gives $E(M)=6(a+b-2)$.

Deleting an edge $uv$ changes its endpoint distance from one to three. The other distances stay fixed. Thus `perturbation` gives $N=M-4(E_{uv}+E_{vu})$. `perturbation_trace` preserves $\operatorname{tr}(HN)$, while `perturbation_commutator` gives an entry $8/a\ne0$ of $HN-NH$. `Trace.trace_lt_energy` gives strictness, `deletion_increases` applies it to a cross edge, and `result` treats every unordered edge.

## Falsifier

A pair of natural part sizes at least two and an edge whose deletion does not strictly increase the zero-diagonal distance Seidel energy would contradict `result`. Disconnected graphs, singleton parts and multiple-edge deletion are outside its hypotheses.

## Evidence

`D5.S3.Combinatorics.Graph.KyFanGap.HarithaChithraDistanceSeidelEnergy.result` proves the complete literal `claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit of `result` is unfinished under [#19628](https://github.com/the-omega-institute/trureturing/issues/19628). No Reg mirror or validated registration is claimed. Missing evidence includes reconstruction of the dependent edge domain, an exact enrolled readout bridge, and whole-family variation and sensitivity.

Experiment: [the published finite check](https://github.com/the-omega-institute/trureturing-experiments/tree/23a1280fffd81c90b7f5f6981dd13a24a390c3c3/docs/reports/haritha-chithra-2022-distance-seidel-energy-problem-5-1). Command: `/tmp/op-lwc-venv/bin/python /Users/auric/trureturing-experiments/docs/reports/haritha-chithra-2022-distance-seidel-energy-problem-5-1/check.py`; exit 0, `RESULT PASS`. Script SHA-256: `d98dd9d8b190718d24a193f64dc33e4f018260d706052b646d596a275a797405`. For every $2\le a\le b\le12$, it checks the perturbation exactly over integers and checks $Mx=3x$ on the first-part side-difference vectors. It numerically checks $E(M)=6(a+b-2)$ and strict energy increase for both diagonal readings, with one representative edge per size pair. At $a=b=12$, the reported zero-diagonal gap is $1.422618$ to six decimal places. These finite computations do not prove a universal statement.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Settlement for every $a,b\ge2$ and every edge | **Proved, kernel-checked:** `result`. |
| Beyond the source's sizes two and three | **Proved, kernel-checked:** specialization of `result` includes those cases and all larger sizes. The attribution of Propositions 5.2–5.3 is a source reading. |
| Baseline energy | **Proved, kernel-checked:** private `baseline_energy` gives $6(a+b-2)$. |
| Trace mechanism and noncommutation | **Proved, kernel-checked:** private `perturbation_trace`, `perturbation_commutator` and `Trace.trace_lt_energy`, consumed by `deletion_increases`. |
| Conditional extension of the mechanism | **Proved, kernel-checked:** private `Trace.trace_lt_energy` applies to any real Hermitian matrix and symmetric involution that do not commute. Applying it to another graph also requires a supporting trace identity; that graph classification is **open**. |
| Semantic admission | The declarations are conservatively classified `bind-only`; admission is `open-problem-resolution (#19532; Proved)`, with `generality: I` and `utility: none`. No general-module escape witness is claimed. |
| Numerical cross-check | **Computed:** exactly the finite scope and evidence in the experiment entry. |
| Source-definition ambiguity | The two diagonal values follow directly from the printed definitions. The diagonal-one universal extension is **open** here; the experiment checks only its finite range. |
| Consequences for the source | **Proved, kernel-checked:** the question has an affirmative answer under the matrix equation. Its two stated partial families remain affirmative. No other theorem in the source is invalidated by this affirmative settlement. |
| Literature | **Open completeness boundary:** the screen in #19532 records the source versions, Scaria–Indulal and Kaliyaperumal–Desikan. The latter's diameter-at-most-two hypothesis does not cover the deleted-edge graph of diameter three. Completeness remains `ASSUMED-UNVERIFIED`. |
| Escape registration | **Open:** the single public theorem is the audit target in #19628; no validated registration is supplied. |

The proof uses pinned Mathlib graph distances, matrix spectral theory, positive semidefinite order and the finite sum-of-squares estimate. It imports no D5 owner. The proof route is supplied by #19532; independent discovery and exhaustive priority are not claimed.

## ASSUMED-UNVERIFIED

Literature completeness, independent priority and exhaustive coverage of subsequent papers are unverified. The literature screen is the bounded source reading in #19532. The unfinished registration boundary is #19628. Finite numerical evidence for the alternative diagonal does not establish its universal extension.
