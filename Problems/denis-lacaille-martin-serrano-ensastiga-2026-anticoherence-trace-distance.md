---
slug: denis-lacaille-martin-serrano-ensastiga-2026-anticoherence-trace-distance
bibkey: denisetal2026anticoherencemixed
doi: 10.48550/arXiv.2605.29436
url: https://arxiv.org/abs/2605.29436v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.result
---

# Trace-distance anticoherence can decrease under covariant spin noise

## Problem

J. Denis, T. Lacaille, J. Martin and E. Serrano-Ensástiga, *Total, quantum, and classical measures of anticoherence for mixed spin states* (2026), arXiv:2605.29436v1, leave the trace-distance case of axiom (T4) open. The downloaded TeX member `arxiv.tex`, line 363, immediately following Proposition 2, states verbatim:

> We also find numerical evidence that axiom~\eqref{ax:T4} remains valid for the trace-distance case $p=1$; a proof is left open.

The TeX label `ax:T4` denotes monotonicity under every completely positive trace-preserving channel covariant under the spin representation of $\mathrm{SU}(2)$ (Definition 2, lines 180–200). Identify a spin-$j$ state $\rho$ with a symmetric state $\rho_S$ of $N=2j$ qubits and put $\rho_t=\operatorname{Tr}_{N-t}(\rho_S)$. In the normalized Dicke basis the reference state is $\rho_0^{(t)}=I_{t+1}/(t+1)$. The source's candidate (lines 333–358) is

$\mathcal A_t^{T,d_1}(\rho)=1-\|\rho_t-\rho_0^{(t)}\|_1/K_t$, with $K_t=\max_{\sigma\in\mathcal D(\mathcal H_{t/2})}\|\sigma-\rho_0^{(t)}\|_1$.

The source uses the full Schatten one-norm. Its mixed-state domain includes every $t\in\{1,\ldots,N\}$; the footnote at line 178 says:

> Whenever we consider pure states, we usually assume $t\le N/2$.

Issue [#24441](https://github.com/the-omega-institute/trureturing/issues/24441) fixes the universal reading: for every integer $N\ge1$, every integer $1\le t\le N$, every such covariant channel $\Phi$, and every positive semidefinite spin-$N/2$ matrix $\rho$ of trace one, $\mathcal A_t^{T,d_1}(\Phi(\rho))\ge\mathcal A_t^{T,d_1}(\rho)$. This assertion is refuted.

The source definitions and locators are collected in [the literature note](../Library/Observer/denisetal2026anticoherencemixed.md).

## Motivation

Axiom (T4) is required for a total anticoherence measure in the source's resource-theoretic framework: covariant noise must not lower the measure. Trace distance is contractive under quantum channels, but here it is evaluated on a reduced state while the channel acts on the full spin space. Whether these two operations support the required contraction decides whether this distance candidate qualifies as a total measure over the stated domain.

## Gap

Issue #24441 records the bounded literature check before any Lean:

- The v1 source retains the open question.
- The search author reports examining the following or citing arXiv records 2606.04681 and 2609.29483, and earlier anticoherence papers 1707.01246, 1409.1106, 1909.07740, 2106.11680 and 2404.15548, without finding a settlement of this trace-distance question.
- The preregistration records no existing repository treatment of the source.
- Full-state trace-distance contraction addresses $t=N$; it does not supply a reduced channel for $t<N$. The source explicitly warns at lines 408–409 that the induced reduced transformation need not be a completely positive trace-preserving channel on the whole reduced state space.

`not-found-in-searched-scope`.

## Route

All lemma names below refer to `AnticoherenceTraceDistanceRefutation` unless qualified otherwise.

1. **The spin-four witnesses.** Set $N=8$, $t=7$ and $\rho=\operatorname{diag}(209,92,560,0,441,0,294,168,0)/1764$ in the Dicke basis indexed by $r=0,\ldots,8$, with $J_z$ entry $4-r$. Put $J_-=J_+^\dagger$ and $c=\sqrt{3/3080}$. The five operators defining `witnessChannel` are $K_0=(3J_z^2-20I)/\sqrt{1540}$, $K_{\pm1}=\mp c(J_zJ_\pm+J_\pm J_z)$ and $K_{\pm2}=cJ_\pm^2$, with $\Phi(X)=\sum_qK_qXK_q^\dagger$. The fixed-witness lemmas `witness_state` and `kraus_complete` establish $\rho\succeq0$, $\operatorname{Tr}\rho=1$ and $\sum_qK_q^\dagger K_q=I$.
2. **Covariance for the full group.** Define $S_{ab}=(J_aJ_b+J_bJ_a)/2-(20/3)\delta_{ab}I$ for axes $a,b\in\{x,y,z\}$. For every complex $9\times9$ matrix $X$, `cartesian_channel` gives $\Phi(X)=(3/770)\sum_{a,b}S_{ab}XS_{ab}$. For every single-qubit $u\in\mathrm{SU}(2)$, `collective_rotation` supplies a real matrix $R$ with $R^{\mathsf T}R=I$ and the rotation law for all three spin-four generators. For every such $u$ and every complex $9\times9$ matrix $X$, `channel_covariant` establishes covariance under $D=\mathrm{spinAction}\,8\,u$. Together with the Kraus certificates, `witness_channel` proves `IsCovariantChannel` for this fixed channel.
3. **The actual qubit reduction.** For natural $N,t$ with $t\le N$ and every complex $(N+1)\times(N+1)$ matrix, `reducedState_eq_dickeSplit` identifies `reducedState` with the partial trace using the Dicke splitting coefficients. Under the same $t\le N$ hypothesis and for every real diagonal input vector, `diagonal_reduction` evaluates this reduction. For the fixed witnesses, `witness_output`, `input_reduction` and `output_reduction` give

   $\rho_7=\operatorname{diag}(21,21,40,21,21,21,21,2)/168$

   and

   $(\Phi(\rho))_7=\operatorname{diag}(69468,87252,64205,82635,78360,59892,43533,32095)/517440$.

   The fixed-witness lemmas `input_distance` and `output_distance` establish $\|\rho_7-I_8/8\|_1=19/84$ and $\|(\Phi(\rho))_7-I_8/8\|_1=3933/17248$.
4. **A meaningful positive normalizer.** At order seven, `normalizer_positive` bounds every distance in the defining supremum by $2$, using positivity and trace one of the state and reference. The rank-one diagonal state supplies an element of that set with distance $7/4$. Thus the set is nonempty and bounded above, and the proof obtains $7/4\le\mathrm{normalizer}\,7$, hence $\mathrm{normalizer}\,7>0$.
5. **Contradiction.** `result` applies the universal `claim` to $N=8$, $t=7$, `witness_channel` and the two hypotheses certified by `witness_state`. Since $19/84<3933/17248$ and the common normalizer is positive, the candidate strictly decreases, contradicting (T4).

## Falsifier

The refutation would miss the source question if the group action, reduction, normalization or order range differed. The module specifies:

- `spinAction` as $V_N^\dagger u^{\otimes N}V_N$, where $V_N$ is the normalized Dicke embedding. Covariance is required for every single-qubit special unitary $u$ and every input matrix.
- `reducedState`, for $t\le N$, by embedding into qubits, explicitly splitting the first $t$ sites from the remaining $N-t$, taking their ordinary partial trace and compressing with $V_t$. Its value for $t>N$ is outside `claim`.
- `normalizer` as the real supremum of the full trace-norm distances over all positive semidefinite trace-one matrices of size $t+1$. The source writes a maximum over the same state space. The contradiction uses only the positivity established at $t=7$ and applies to any positive normalization; it needs neither attainment of the supremum nor an exact normalizer value.
- `claim` with $N\ge1$ and the full mixed-state range $1\le t\le N$. The mixed witness at $t=7>N/2$ lies in that range.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.lean`.

- **Proof.** It defines `spinAction`, `reducedState`, `normalizer`, `anticoherence`, `IsCovariantChannel` and `claim`, and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/AnticoherenceTraceDistanceRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:695f53ac6175b1e7b2a4079ad92232389c1f18b7e879f66d64d53cbb9f85e66c`;
- `claim`: `sha256:b4d9040740ae73f1d68b7d5c5fd0d24045937a0d519adc2b047a9e3349a53700`.

## Triage

Tier 1 question left open in a 2026 preprint, preregistered in issue #24441 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural $N\ge1$, every natural $1\le t\le N$, every completely positive trace-preserving complex-linear map covariant under `spinAction` on all input matrices, and every positive semidefinite trace-one spin-$N/2$ matrix $\rho$, `anticoherence` at $\rho$ is at most `anticoherence` at its channel output.

**Computed, not formalized**. None.

**Argued, not formalized.**

- *The missing reduced operation.* Let $R_t$ denote the qubit reduction. A sufficient additional condition is a positive trace-preserving map $\Psi_t$ on the entire reduced matrix algebra that fixes $I_{t+1}/(t+1)$ and satisfies $R_t\Phi=\Psi_tR_t$ on every full density matrix. For Hermitian $H=H_+-H_-$, positivity, the triangle inequality and trace preservation give $\|\Psi_t(H)\|_1\le\operatorname{Tr}H_++\operatorname{Tr}H_-=\|H\|_1$. Apply this to $H=R_t(\rho)-I_{t+1}/(t+1)$; for any positive $K_t$, (T4) follows. The two distances certified by `input_distance` and `output_distance` for the fixed $N=8$, $t=7$ witnesses exclude such a map $\Psi_7$ for this channel. Covariance of the full channel alone does not provide this missing structure.
- *Why the Schatten-two argument does not transfer.* The source's Appendix proof of Proposition 2, lines 1358–1384, expresses the squared Hilbert–Schmidt distance as a sum of squared multipole coefficients and bounds each summand using $|f_L|\le1$. That diagonal sum-of-squares argument does not bound the trace norm. The witness already consists of diagonal reduced matrices: the failure concerns their eigenvalue deviations from the mixed reference, without requiring off-diagonal reduced entries.
- *Surviving channel restrictions.* For $t=N\ge1$, covariance on the irreducible spin sector makes $\Phi(I)$ commute with every spin rotation; Schur's lemma and trace preservation give $\Phi(I)=I$. The preceding contraction argument applies directly. For any $1\le t\le N$, a convex mixture of global spin rotations intertwines with reduction term by term; the same mixture of reduced rotations is a positive trace-preserving map fixing the reduced reference, so that argument applies again. In both cases the normalizer is positive: a rank-one reduced state has distance $2t/(t+1)>0$, while the triangle inequality bounds all defining distances by $2$.
- *Remaining order range.* Whether the trace-distance candidate satisfies (T4) throughout $1\le t\le N/2$ remains open here. The counterexample supplies no conclusion about that restricted universal statement or about the smallest spin admitting a violation.
- *Effect on the source.* Over its full mixed-state range, the trace-distance candidate cannot meet the total-measure definition because (T4) is required. The conditional convex-roof proposition at lines 477–480 assumes that its chosen total distance quantity satisfies the total-measure axioms; its specialization to the trace-distance candidate therefore lacks that hypothesis at the exhibited spin and order. The conditional proposition itself is not refuted. The source's purity and Hilbert–Schmidt monotonicity arguments do not depend on the trace-distance conjecture. Its separate fidelity-based (T4) question, and its quantum and classical constructions using other candidates, receive no settlement from `result`.

## ASSUMED-UNVERIFIED

The literature check in #24441 is bounded and does not establish exhaustive worldwide novelty or priority. The reported readings of the two following or citing records and five earlier papers were not independently reproduced; neither were the issue's random-state searches or floating-point covariance and trace-preservation residuals. Those searches do not settle the restricted range $t\le N/2$.

The arguments labelled above are not formalized. In particular, the module does not establish an exact formula for the normalizer, a general reduced-channel contraction theorem, the surviving channel restrictions, a minimal counterexample dimension, or a classification of violations. The maximum-versus-supremum identification and the source's other measure axioms and constructions have not been formally audited by this settlement.
