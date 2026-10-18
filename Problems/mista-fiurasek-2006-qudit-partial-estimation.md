---
slug: mista-fiurasek-2006-qudit-partial-estimation
bibkey: mista2006partialestimation
doi: 10.1103/PhysRevA.74.022316
url: https://arxiv.org/abs/quant-ph/0606112
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result
---

# The Mišta–Fiurášek qudit partial-estimation trade-off

## Problem

L. Mišta Jr. and J. Fiurášek, *Optimal partial estimation of quantum states from several copies*, arXiv:quant-ph/0606112v1, Phys. Rev. A 74, 022316, Introduction, Eq. (2), states:

> Moreover, we also conjecture that the optimal fidelity trade-off for an ensemble of N identical pure states of a d-level system has the form

$$
\sqrt{F-\frac1{N+d}}=
\sqrt{(d-1)\left(\frac{N+1}{N+d}-G\right)}+
\sqrt{N\left(G-\frac N{N+d}\right)}.
$$

[Preregistration #16777](https://github.com/the-omega-institute/trureturing/issues/16777) fixes the literal covariance-reduced PSD-seed model. The source is documented in [the Library note](../Library/QuantumChannels/mista2006partialestimation.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $N$ copies of a $d$-level pure state, $N\ge1$, $d\ge2$ | `claim` quantifies natural `N`, `d` with precisely these two inequalities | Every allowed dimension and copy count is retained. |
| Symmetric input space tensored with one output qudit | The carrier is the product of the literal occupation subtype $\{n:\mathrm{Fin}(d)\to\mathbb N\mid\sum_i n_i=N\}$ with `Fin d` | Occupation carriers occur inline; no alternate certificate space replaces them. |
| Eq. (12), the partial transpose of the symmetric projector | `OccupationPartialTransposeSpectral.RF`, `symmetricProjector`, `occupationEmbedding` | The normalized word-sector projector, partial transpose and compression are the definitions. Entry formulas are proved afterward. |
| Eq. (10), reference projection and output partial trace | `OccupationPartialTransposeSpectral.RG`, `outputReferenceProjector`, reused `PartialTraceMutualInformation.partialTraceRight` | The matrix product, partial trace and tensor with the output identity are retained. |
| Positive seed and Schur normalization | `chi.PosSemidef` and trace equal to the complex coercion of $\binom{N+d-1}{d-1}$ | No rank restriction is imposed on competitors. |
| Output and estimation fidelities | Real parts of `trace (chi * RF N d)` and `trace (chi * RG N d)` | Both scores use the literal source operators. |
| $N/(N+d-1)\le G\le(N+1)/(N+d)$ | The two bounds on real `G` in `claim` | The complete closed interval, including endpoints, is retained. |
| Optimal curve, Eq. (2) | `IsGreatest` of the set of all feasible output scores at fixed `G` | The displayed squared curve is both attained and an upper bound. Its square-root terms are nonnegative on the stated interval, so it is equivalent to Eq. (2). |
| Proof of the conjecture | `QuditPartialEstimationTradeoff.result : claim` | There are no additional hypotheses. |

## Motivation

The result gives the exact information–disturbance frontier for all copy counts and qudit dimensions in the source's PSD-seed optimization. The optimization includes every positive semidefinite seed with the specified trace and estimation score. An explicit rank-one seed attains each frontier point.

## Gap

The source proves the qubit trade-off and conjectures Eq. (2) for general qudits. The literature screen recorded in #16777 covers eight citing works and Rapčan's thesis, which describes the qudit case as a conjecture. No screened work settles Eq. (2) for $d\ge3$. Completeness of that screen is `ASSUMED-UNVERIFIED`.

## Route

In `OccupationPartialTransposeSpectral`, the occupation indices are partitioned into coupled blocks and isolated singletons. `BlockMatrices.weighted_block` identifies each coupled restriction as an identity term plus a rank-one term and one distinguished coordinate. `GlobalBound.global_operator_bound` combines the exhaustive decomposition with the scalar Rayleigh estimate and monotonic domination by the all-reference block.

In `QuditPartialEstimationTradeoff`, private `Scores.seed_support_bound` transfers that matrix inequality to the literal seed fidelities. Private `ScalarAssembly.scalar_frontier` supplies the scalar supporting-line argument, including the endpoint. Private `Attainment.frontierSeed_scores` computes the attaining seed's two fidelities; `frontierSeed_psd` and `frontierSeed_trace` give feasibility. `result` assembles the upper bound and attainment into `IsGreatest`.

## Falsifier

A PSD seed with the specified trace and estimation score and an output score strictly above the curve would contradict `result`. A discrepancy between the source's operators and the formal definitions would invalidate the model correspondence. The theorem does not independently establish the published covariance/Choi reduction from arbitrary instruments and Haar averages.

## Evidence

The mathematical declarations are in [OccupationPartialTransposeSpectral](../D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral.lean) and [QuditPartialEstimationTradeoff](../D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.lean). The settling declaration is `D5/S3/Quantum/Measurement/QuditPartialEstimationTradeoff.result`; no atom or coverage claim is involved.

The four-slot escape audit is unfinished: [#17100](https://github.com/the-omega-institute/trureturing/issues/17100). It covers the new public theorems and the publicized or relocated owner declarations. Missing reconstruction, source-selection, bridge and sensitivity evidence is not a `declared_validated` registration.

### Numerical check

The independent finite check is [the experiment directory at commit `cce08e4484a3406292ef841a8536a46d3ceafd0c`](https://github.com/the-omega-institute/trureturing-experiments/tree/cce08e4484a3406292ef841a8536a46d3ceafd0c/docs/reports/mista-fiurasek-2006-qudit-partial-estimation-tradeoff). Command: `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 check.py` from that directory; exit 0, `ALL_OK`. The script SHA-256 is `4ab2bfe6df891c3735e092664300c532c74ff26a75f3ef5941debdfc7f4de6b5`.

For $d\in\{2,3,4\}$ and $N\in\{1,2,3,4\}$, the program constructs the source matrices and compares their maximal-eigenvalue support with the closed form and the curve support at 41 weights. The curve support uses a 4001-point grid. All 12 pairs pass; the largest reported deviation is $1.23\times10^{-7}$. These finite numerical comparisons are separate from the theorem for all $N,d$; they provide no uniform numerical error theorem.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Exhaustive occupation blocks, each rank one plus a coordinate term | Proved, kernel-checked: `OccupationPartialTransposeSpectral.BlockMatrices.weighted_block` and private `Global.weighted_decomposition` | Every coupled block and isolated singleton is included. |
| All-reference domination and scalar support reduction | Proved, kernel-checked: `OccupationPartialTransposeSpectral.GlobalBound.global_operator_bound`; private `QuditPartialEstimationTradeoff.Scores.seed_support_bound` and `ScalarAssembly.scalar_frontier` | The block bound is uniform in the occupation and the supporting parameter. |
| Attainment by a rank-one seed | Proved, kernel-checked: private `QuditPartialEstimationTradeoff.Attainment.frontierSeed_psd`, `frontierSeed_trace`, `frontierSeed_scores`, and public `result` | A feasible seed attains every allowed frontier score. |
| Eq. (2) for all $N\ge1$, $d\ge2$ | Proved, kernel-checked: `QuditPartialEstimationTradeoff.result` | This is the literal PSD-seed optimization, without an arbitrary-instrument formalization. |
| Single-copy and qubit cases | Proved as specializations of `result` at $N=1$ and $d=2$ | The source identifies the $N=1$ balance with Banaszek, PRL 86, 1366 (2001), reference [7], and proves the qubit curve as Eq. (1). Substitution into the displayed curve recovers those parameter cases; no separate operational theorem is claimed. |
| Published covariance/Choi reduction | Input from the source, Section II, Eqs. (3)–(14) | The reduction from arbitrary instruments to PSD seeds is not separately formalized. |
| Arbitrary-instrument operational statement | Open | Instruments, Haar averages and the covariance reduction require an additional formal layer. |
| Mixed-state and multi-output variants | Open | The theorem concerns identical pure inputs and one output qudit. |
| Finite matrix/support experiment | Computed: the pinned experiment entry above, command exit 0 and the stated SHA-256 | Exactly the 12 pairs, 41 weights and 4001-point curve grid specified above; `ALL_OK`, maximum reported deviation $1.23\times10^{-7}$. |
| Eight citing works and Rapčan's thesis | Literature reading recorded in #16777; completeness `ASSUMED-UNVERIFIED` | None of the screened sources settles Eq. (2) for $d\ge3$. |

The argument supplies a general-dimension proof of the conjectured seed frontier. The source's covariance reduction remains an input. No unformalized source result depending on that operational reduction is reclassified as kernel-checked here.

## ASSUMED-UNVERIFIED

The literature screen is not exhaustive. Publication priority beyond the screened sources remains unverified. The instrument-to-seed reduction is a published premise of the model correspondence, not a theorem of these modules. The four-slot escape audit remains unfinished under #17100.
