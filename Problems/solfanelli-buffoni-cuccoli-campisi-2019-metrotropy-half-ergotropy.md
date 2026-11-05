---
slug: solfanelli-buffoni-cuccoli-campisi-2019-metrotropy-half-ergotropy
bibkey: solfanellibuffonicuccolicampisi2019metrotropy
doi: 10.1088/1742-5468/ab3721
url: https://arxiv.org/abs/1905.10262v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result
---

# Measurement can extract more than half the ergotropy of a non-stationary state

## Problem

A. Solfanelli, L. Buffoni, A. Cuccoli and M. Campisi, *Maximal energy extraction via quantum measurement*, J. Stat. Mech. (2019) 094003, arXiv:1905.10262v2, compare the metrotropy $\mathcal M$, the maximal energy extractable by a non-selective rank-one projective measurement, with the ergotropy $\mathcal W$, the maximal energy extractable by a unitary. For stationary states they prove $\mathcal M\le\mathcal W/2$; for non-stationary states they prove $\mathcal M\le\mathcal W$. Section 3.1 of the source TeX `Metrotropy02.tex`, lines 277–308, ends:

> Whether the relation $\mathcal M \leq \mathcal W/2$ holds in the case $[H,\rho]\neq 0$ remains an open question.

The repository proposition `claim` reads the question for finite dimensions. For every $d$ and all $d\times d$ complex matrices $h,\rho$ with $h$ Hermitian, $\rho$ a density matrix and $h\rho\ne\rho h$,
\[
\operatorname{metrotropy}(h,\rho)\le\operatorname{ergotropy}(h,\rho)/2 .
\]
Here `measured u ρ` is the non-selective measurement $\sum_k\pi_k\rho\pi_k$ with $\pi_k$ the projector onto the $k$th column of a unitary $u$; `metrotropy h ρ` is $\operatorname{Re}\operatorname{Tr}(h\rho)$ minus the infimum of the energies of `measured u ρ` over all unitaries $u$; `ergotropy h ρ` is $\operatorname{Re}\operatorname{Tr}(h\rho)$ minus the infimum of the energies of $v\rho v^\dagger$ over all unitaries $v$.

The Lean declaration is `result : \lnot claim`.

## Motivation

A positive answer would make unitary driving at least twice as effective as any rank-one measurement for extracting energy from every finite quantum system, extending the stationary bound of the source to states with coherence in the energy basis. A counterexample shows that coherence lets a measurement remove more energy than the stationary analysis permits, and that the general bound $\mathcal M\le\mathcal W$ of the source cannot be halved.

## Gap

The bounded literature check recorded in issue [#23607](https://github.com/the-omega-institute/trureturing/issues/23607) found no settlement in the source, its citing works or the repository records; the search scope is recorded in that issue.

`not-found-in-searched-scope`.

## Route

1. The module defines `measured`, `metrotropy`, `ergotropy` and `claim` as above. It reuses the frozen definitions `expect` (energy $\operatorname{Re}\operatorname{Tr}(h\sigma)$), `rankOneDensity`, `unitaryEvolution`, `measurementProjector`, `krausApply` and `IsDensity`, and the frozen theorems `sum_projectors` and `kraus_psd`.
2. The witness is $h=\operatorname{diag}(0,1,2,10)$ and $\psi=(0,0,\tfrac{3i}5,\tfrac45)$ with $\rho=|\psi\rangle\langle\psi|$. The private lemmas `h4_hermitian` and `rho4_trace` give the hypotheses on $h$ and $\rho$, and `commutator_entry` computes $(h\rho-\rho h)_{23}=-\tfrac{96}{25}i$, so `h4_commutator` gives $h\rho\ne\rho h$.
3. For the unitary $u=\tfrac12\begin{pmatrix}1&1&1&1\\1&-1&1&-1\\1&1&-1&-1\\1&-1&-1&1\end{pmatrix}$ (`u4_unitary`), every outcome probability equals $\tfrac14$ (`u4_probability`), so `measured_u4` gives the measured state $I/4$. `energy_rho4` and `energy_measured_u4` give the energies $\tfrac{178}{25}$ and $\tfrac{13}4$.
4. Every measured state and every unitary image of $\rho$ is positive semidefinite, and $h$ is diagonal with nonnegative entries, so their energies are nonnegative (`energy_nonneg`). Hence the infimum over measurements is at most $\tfrac{13}4$, giving $\operatorname{metrotropy}(h,\rho)\ge\tfrac{387}{100}$ (`metrotropy_lower`), and the infimum over unitaries is nonnegative, giving $\operatorname{ergotropy}(h,\rho)\le\tfrac{178}{25}$ (`ergotropy_upper`).
5. Since $\tfrac{387}{100}>\tfrac{89}{25}=\tfrac{356}{100}$, `instance_violates` contradicts the inequality, and `result` applies `claim` at $d=4$, this $h$ and this $\rho$.

## Falsifier

The refutation would not apply to the source question if the module's notions differed from the source's: a measurement other than a complete set of rank-one orthogonal projectors applied non-selectively, an energy other than $\operatorname{Tr}H\rho$, or optimizations over a smaller set than all orthonormal bases and all unitaries. The module optimizes with infima, so it uses only one admissible measurement and the lower bound $0$ on unitary energies; it does not compute the exact metrotropy or ergotropy of the instance. It covers finite-dimensional systems and rank-one projective measurements only.

## Evidence

The canonical source is `D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** `#print axioms` on `result` reports only `propext`, `Classical.choice`, and `Quot.sound`; the module contains no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:c8a4037b551d9d21286531d996f68ddf3fdd99117aeada94f270800fce94b1eb`;
- `claim`: `sha256:f79c95cd19223c8484864cbd2eb2457ea115ac44753681dc5cc3454173601fba`.

## Triage

Tier 1 open question of a 2019 J. Stat. Mech. paper, preregistered in issue #23607 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; its per-declaration proof shapes are bind-only definitions and private lemmas consumed on the proof path of `result`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the formal proposition `claim` is false.

**Argued, not formalized.**

- The mechanism is coherence. For a stationary state the outcome probabilities $\langle u_k|\rho|u_k\rangle$ are a doubly stochastic transform of the populations, which limits how much population a measurement can move downward. With coherence in the energy basis, the probabilities also contain the off-diagonal terms, so a basis unbiased with respect to $\psi$ sends the pure state to $I/d$ and removes its high-energy population, as in the witness.
- The same construction suggests that $\mathcal M/\mathcal W$ can approach $1$. Take a pure non-stationary state close to the top eigenvector of $H=\operatorname{diag}(0,\dots,0,1)$ and a basis unbiased with respect to it. Then $\mathcal M\ge E-\operatorname{Tr}H/d$ while $\mathcal W=E$, so the ratio is at least about $1-1/d$. This matches the source's general bound $\mathcal M\le\mathcal W$ asymptotically; no sharp constant is claimed.
- The source's stationary bound $\mathcal M\le\mathcal W/2$ is unaffected. A bound interpolating between $\mathcal W/2$ and $\mathcal W$ in terms of a coherence measure could survive; this module does not prove one.

## ASSUMED-UNVERIFIED

The literature check is bounded to the source, the citing works and the repository searches recorded in issue #23607; it does not establish exhaustive worldwide novelty or priority. The exact metrotropy and ergotropy of the witness, the asymptotic ratio argument, the mechanism discussion and any coherence-dependent bound remain unverified by this module.
