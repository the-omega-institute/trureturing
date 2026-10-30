---
slug: mmd2205-seidelchain
bibkey: mandalmehataridas2022seidelchain
doi: 10.48550/arXiv.2205.00310
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.result
url: https://arxiv.org/abs/2205.00310v1
---

# Minimum Seidel energy of chain graphs

## Problem

Santanu Mandal, Ranjit Mehatari and Kinkar Chandra Das, *On the spectrum and energy of Seidel matrix for chain graphs*, arXiv:2205.00310v1, Conjecture 4.14:

> Let $G$ be a chain graph of order $n$ with the binary string $b=0^{s_1}1^{t_1}0^{s_2}\ldots0^{s_k}1^{t_k}$ such that $\sum_i(s_i+t_i)=n$, $s_i\ge1$ and $t_i\ge1$. Then $SE(G)\ge SE(H)$, where $H\in\Gamma_{n,k}$. Moreover, the equality holds if and only if $G\in\Gamma_{n,k}$.

Here $\Gamma_{n,k}$ has binary word $0^{s_1}(10)^{k-1}1^{t_k}$ with positive endpoints, each at most $n-2k+1$, and $s_1+t_k=n-2k+2$. Seidel matrices are $J-I-2A$ and energy sums the absolute eigenvalues with multiplicity. The theorem quantifies over every comparator $H$.

### Statement echo

The local names below belong to `D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum`; the five graph conventions lie in its `MandalMehatariDasSeidel` namespace.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive alternating runs $0^{s_1}1^{t_1}\cdots0^{s_k}1^{t_k}$ | `binaryString`, positive hypotheses in `claim` | All run lengths and their order are retained. |
| A later 1 is adjacent precisely to earlier 0-vertices | `chainGraph` | The symmetric adjacency relation has no loops. |
| Order $n$ | Sum hypothesis in `claim` | The vertices are the positions of the binary list; its length is the sum of the runs. |
| $S=J-I-2A$ | `seidel` | Literal all-ones matrix, identity and scalar adjacency matrix. |
| $SE$ is the sum of absolute eigenvalues | `energy`, `energy_eigenvalues` | Real characteristic roots with multiplicity; every graph matrix used is real symmetric. |
| Every $H\in\Gamma_{n,k}$ | Universal list `h` and `Gamma n k h` in `claim` | No representative comparator is substituted. |
| Minimum and equality precisely in $\Gamma_{n,k}$ | Both conclusions of `claim`, proved by `MandalMehatariDasSeidel.result` | Full inequality and equivalence, including $k=1$. |
| $k\ge1$ and $2k\le n$ | Explicit guards in `claim` | These follow from nonempty positive runs and introduce no source restriction. |
| Finite ordered vertices | `Fin` and the finite type instances | These encode the finite graph and its construction order. |

Standalone `Gamma` outside $1\le k$ and $2k\le n$ is outside the source interpretation: natural subtraction truncates. The settling proposition has both guards. The literal binary and Seidel conventions are retained; the proofs also use shared spectral owners.

## Motivation

The settling GID is `D5/S3/Combinatorics/Graph/KyFanGap/MandalMehatariDasSeidelMinimum.result`, with admission basis `open-problem-resolution (#21681; Proved)`, `generality: G` and `utility: none`. The source and literal conventions are recorded in [#21681](https://github.com/the-omega-institute/trureturing/issues/21681) and `Library/GraphInvariants/mandalmehataridas2022seidelchain.md`.

## Gap

The minimum and its complete equality characterization are settled for every admissible order and run count. No assertion is made about arbitrary other blow-up cores, disconnected chain graphs or the source's distinct-eigenvalue questions. Literature completeness remains `ASSUMED-UNVERIFIED`.

## Route

For $k\ge2$, put $d=2k-1$. Sign switching merges the first 0-run with the last 1-run. The private `MMDGraphCompression.switched_compression` identifies the switched matrix with a class-indicator compression of the signed odd core. Its weights are $x_0=s_1+t_k$ and the intermediate run sizes, so $x_0>1$ and every $x_i\ge1$.

The private `MMDVariational.variational_formula` represents the trace of the absolute compressed core as the minimum of an objective linear in the diagonal weights. `MMDStrictness.no_common_vertex_equations` excludes a common positive-definite minimizer at two distinct simplex vertices. Signed rotation gives equal values at the vertices; `MMDCoreMinimum.core_diagonal_minimum` gives the minimum and forces every nonbase weight to be one in the equality case.

`MMDMatrixEnergy.compressed_energy` retains the core positive inertia index symbolically. The index is constant under invertible diagonal congruence, so the energy correction cancels in the comparison; its explicit Fourier count is unnecessary. `MMDGraphEnergy.binary_minimum` and `MMDGraphEnergy.gamma_minimum` identify the admissible words and all comparators. For $k=1$, `MMDBoundary.result_one` uses the common switched matrix $J-I$ without requiring a numerical evaluation of its energy. The public result combines both cases.

## Falsifier

An admissible positive run family and a Gamma comparator violating either the energy inequality or its equality characterization would contradict the settling `result`. A counterexample without the guards or to another graph core would not contradict it.

## Evidence

`D5.S3.Combinatorics.Graph.KyFanGap.MandalMehatariDasSeidelMinimum.MandalMehatariDasSeidel.result` proves the literal complete `claim`. The supporting declarations named in Route are private declarations of the same module. The public spectral identities are `Spectral.sum_abs_eq_trace_sqrt` and `energy_eigenvalues`.

The escape audit of the three source-authored public theorems, the compiler-generated `energy.congr_simp` and `invRootDiagonal.congr_simp` companions, and the published owner definition `D5.S3.Observer.Hankel.BalancedHankelSchmidt.invRootDiagonal` is unfinished under [#22032](https://github.com/the-omega-institute/trureturing/issues/22032). No Reg mirror or validated four-slot registration is supplied. The missing evidence comprises source reconstruction, an exact lawful enrolled readout bridge, whole-family variation/sensitivity and observational dependence.

Experiment: [the finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/f1f7a0711f88f1ffb836d47e29e7a83ec51625f0/docs/reports/mmd-seidel-chain), commit `f1f7a0711f88f1ffb836d47e29e7a83ec51625f0`, file `docs/reports/mmd-seidel-chain/check.py`, SHA-256 `2c921a1141089050e3708af9184af68236d8665232e7ce1fd508542d4b2e47b3`. Command: `/tmp/op-mmd2205/venv/bin/python -u /Users/auric/.sshx/19a0b4a433281e2b662228bc/attempt-1/check.py`; exit 0, final result `ALL_CHECKS_OK`, SymPy 1.14.0. It verifies 66 endpoint choices in $\Gamma_{n,2}$ for $4\le n\le14$, inverse/signed-rotation identities for 11 cores with $2\le k\le12$, and all 511 positive compositions of even length for $2\le n\le10$. Exact characteristic polynomials and rational root isolation of width at most $10^{-16}$ give 416 strict cases, 95 equality cases and 466 gap/inertia certificates. No floating-point comparison is evidence, and these finite checks do not establish a universal extension.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Every admissible chain graph has at least the energy of every Gamma comparator; equality iff its binary string belongs to Gamma | **Proved, kernel-checked:** `MandalMehatariDasSeidel.result`, including both quantified conclusions. |
| For every odd $d\ge3$, the compressed-core minimum for arbitrary real weights $x_i\ge1$ with $x_0>1$ | **Proved, kernel-checked:** private `MMDCoreMinimum.core_diagonal_minimum` and `MMDMatrixEnergy.core_energy_minimum`, including their equality cases. |
| The inertia correction is constant as the weights vary; an explicit Fourier inertia count is unnecessary | **Proved, kernel-checked:** private `MMDMatrixEnergy.compressed_energy`; the symbolic positive inertia index of the fixed core is independent of the weight vector. No explicit index formula is asserted. |
| Checker result: 66 source cases, 11 cores, 511 compositions, 416 strict, 95 equality and 466 gap/inertia certificates | **Computed:** the immutable checker, command, exit 0, hash and exact finite ranges in Evidence. |
| Analogous minima for other graph blow-up cores | **Open:** those cores require their own transitive signed symmetries and strictness conditions; no such conclusion is asserted. |
| Distinct Seidel eigenvalue problems | **Open here:** these lie outside the settling proposition. The literature screen identifies Xiong–Hou, arXiv:2310.20230v1, as addressing some related eigenvalue questions. |
| Consequences for the source | **Proved, kernel-checked:** the source's $k=2$ minimum is a specialization of `result`; all larger admissible run counts and the complete equality case are included. The source's final conjecture is settled without invalidating any of its preceding results. |
| Literature | **Open completeness boundary:** the screen in #21681 reads the source, Mandal arXiv:2308.00340v1, Xiong–Hou arXiv:2310.20230v1 and the relevant later papers. No settlement was located in that searched scope; completeness is `ASSUMED-UNVERIFIED`. |
| Escape registration | **Open:** the three source-authored public theorem targets, their two new public compiler-generated companions and the published owner definition are listed in #22032; no `declared_validated` status is claimed. |

## ASSUMED-UNVERIFIED

The literature screen is bounded: citation-list APIs were unavailable; exact author-name searches do not cover every variant; an unindexed journal version is not excluded. Global absence of a prior settlement and independent priority remain unverified. Finite experiment results do not establish claims beyond their stated ranges. The escape audit remains unfinished under #22032.
