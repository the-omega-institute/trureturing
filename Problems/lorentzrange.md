---
slug: lorentzrange
bibkey: chengchen2026lorentzrange
doi: null
url: https://arxiv.org/abs/2605.19530v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.result
---

# Cheng–Chen Conjecture 24: odd-qubit Lorentz invariant range

## Problem

Y. Cheng and L. Chen, *Construction of three-qubit positive-partial-transpose entangled states of rank four*, arXiv:2605.19530v2, Conjecture 24, state:

> Suppose ρ is an arbitrary n-qubit state with odd n, then the range of Lorentz invariant Iρ is [−1/2, 0].

Definition 12 gives $\epsilon=\begin{pmatrix}0&1\\-1&0\end{pmatrix}$ and $\epsilon_n=\epsilon^{\otimes n}$. Equation (54) defines $I_\rho=\operatorname{Tr}(\rho^T\epsilon_n\rho\epsilon_n)$. A state is a complex positive semidefinite matrix of trace one. Preregistration: [#18697](https://github.com/the-omega-institute/trureturing/issues/18697).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Definition 12: two-dimensional Levi-Civita symbol | `eps` | Literal matrix with entries $0,1,-1,0$. |
| Definition 12: tensor product of $n$ copies | `epsN n` | Entrywise finite product over `Fin n`, indexed by bit strings `Fin n → Fin 2`. |
| Arbitrary $n$-qubit state | `IsState` | Positive semidefinite and trace one; no rank, PPT or separability restriction. |
| Equation (54): complex trace of the four-factor product | `lorentz` | Transpose, followed by $\epsilon_n$, the state, and $\epsilon_n$ in the stated order. |
| Every odd $n$ | `claim`, `∀ n : ℕ, Odd n → …` | Oddness already implies $n\ge1$; no additional premise. |
| The range is exactly $[-1/2,0]$ | `claim`, set equality with the complex image of `Set.Icc` | Both containment and attainment, including reality. |
| Whole conjecture | `result` | Unconditional proof of `claim`. |

All five public definitions have the bodies fixed by the preregistration. The reused proof ingredients retain those public definitions.

## Motivation

The kernel-checked settling declaration is `D5.S3.Quantum.Entanglement.Lorentz.ChengChenLorentzInvariantRange.result`. It proves the whole range for every odd number of qubits. The module's admission basis is `open-problem-resolution (#18697; Proved)`; its proof shape is `bind-only`, with no escape witness claimed.

## Gap

The source computes special states in Lemmas 22–23 and states the odd-$n$ range as Conjecture 24. The exact interval, including every intermediate value and the fact that no imaginary part occurs, is the settled assertion.

## Route

For odd $n$, put $E=\epsilon_n$ and $B=EA^TE^\dagger$. Skew symmetry and unitarity make the flipped vector $E\overline v$ a unit vector orthogonal to $v$. The private `breuer_psd` proves $(1-A-B).\mathrm{PosSemidef}$ from positivity and trace one of $A$. It uses `spectral_mixture`, `pair_complement_psd`, `flip_norm`, `skew_dot_zero` and `flip_rank_one`.

The private `overlap_bound` applies `RHLinalg.trace_mul_nonneg_of_posSemidef` to bound $\operatorname{Re}\operatorname{Tr}(AB)$ between $0$ and $1/2$. The private `trace_mul_real` uses `D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian` after finite reindexing. Cyclicity then gives $I_A=-\operatorname{Tr}(AB)$.

The private `pair_lorentz` evaluates the diagonal two-basis state with weights $p$ and $1-p$ as $-2p(1-p)$. The private `attained` chooses $p=(1-\sqrt{1+2x})/2$ for $x\in[-1/2,0]$. This explicit construction supplies every value without an intermediate value theorem.

## Falsifier

A counterexample to the settled statement would be an odd $n$ and a positive semidefinite trace-one matrix whose invariant is outside the real interval, or a point of that interval which no state attains. `result` excludes both possibilities under the displayed definitions and the accepted axiom closure.

## Evidence

Kernel evidence is the frozen settling module and its `result`; the only public theorem is `result`. The private lemmas named in Route are proof ingredients of that theorem. No independent escape witness is asserted.

The supplementary experiment is [cheng-chen-2026-lorentz-invariant-range at f16e92daa5f92f593895e8eac69fed4c636b2fad](https://github.com/the-omega-institute/trureturing-experiments/tree/f16e92daa5f92f593895e8eac69fed4c636b2fad/docs/reports/cheng-chen-2026-lorentz-invariant-range). Command: `python3 /Users/auric/trureturing-experiments/docs/reports/cheng-chen-2026-lorentz-invariant-range/check.py 20000 1`; exit $0$, `RESULT PASS`; script SHA-256 `6347ad3372472a7c1b240c868f27c3ce12d0e84df28625e97255b84225b1b388`. The local script is byte-identical to that immutable revision.

The experiment samples 20,000 states at each of $n=1,3,5$ using NumPy double precision, with sampled ranks chosen from all ranks. The observed real ranges are $[-0.499233,2.78\cdot10^{-16}]$, $[-0.370964,1.07\cdot10^{-16}]$ and $[-0.087471,2.63\cdot10^{-17}]$, respectively; maximum imaginary magnitudes are $8.3\cdot10^{-17}$, $3.8\cdot10^{-17}$ and $2.1\cdot10^{-17}$. It checks pure and mixed-pair endpoints and 101 segment points for each of those three qubit counts. Fraction arithmetic checks the exact $n=1$ values $0$ and $-1/2$. At $n=2$, the Bell-state contrast evaluates to $1.000000$ in double precision. These finite readings supplement the universal Lean proof.

The escape audit of `result` is unfinished: [#19827](https://github.com/the-omega-institute/trureturing/issues/19827). No Reg mirror or `declared_validated` registration is claimed. A faithful dependent-family reconstruction, equivalence bridge, enrolled readout and variation/sensitivity/observational-dependence evidence are missing.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Exact conjecture under the binding definitions | **Proved, kernel-checked:** `result` equates the full odd-$n$ range with the complex image of $[-1/2,0]`. |
| Load-bearing Breuer estimate | **Proved, kernel-checked:** private `breuer_psd` proves $(1-A-EA^TE^\dagger).\mathrm{PosSemidef}$ for every finite index type, trace-one PSD $A$, and skew-unitary $E$. This is not asserted as an escape witness. |
| Proof route and attainment | **Proved, kernel-checked:** private `pair_lorentz` and `attained` give the explicit two-basis diagonal family and square-root parameter. No continuity hypothesis is added. |
| Supplementary checker | **Computed:** the experiment in Evidence checks exactly $n=1,3,5$, 20,000 random states per count, the stated endpoint and segment checks, and the $n=2$ contrast; command, exit and immutable script identity are given there. |
| Even-$n$ contrast | **Computed:** the same experiment gives $I\approx1$ at one Bell state with $n=2$. The full even-$n$ range is **open** here. |
| All minimizers | **Open:** the proposed characterization by $A=B$ and $A+B$ being a rank-two projection is not proved here. The module proves attainment but no exhaustive classification. |
| Source Lemmas 22–23 | **Proved in prose, for their odd-$n$ range consequence:** any of their states satisfying the stated state hypotheses is an instance of the universal range equality. Their other structural statements are not asserted by this module. |
| Literature status | **Literature reading:** #18697 records the source v2 and Breuer's arXiv:quant-ph/0605036, Eqs. (1)–(3), and a search without a settlement in arXiv/OpenAlex, quant-ph/0307124, quant-ph/0402051, arXiv:1407.8195, formal-conjectures and the repository. Completeness is `ASSUMED-UNVERIFIED`. |
| Freeze and admission | **Computed, machine evidence:** the canonical deposit writes the settling module state; required CI supplies admission checks. This dossier is not a second state registry. |
| Escape registration | **Open:** unfinished audit #19827; no validated registration. |

The decisive structure is the positive complement of a state and its skew-unitary partner. The scalar overlap estimate holds for arbitrary finite-dimensional PSD $A,B$ of trace one with positive complement, as stated by private `overlap_bound`. The full range is sharp because `attained` supplies both endpoints and every intermediate value. Extensions to even $n$ and a classification of minimizers are distinct questions.

## ASSUMED-UNVERIFIED

Literature-search completeness is `ASSUMED-UNVERIFIED`; absence of a hit is limited to the sources and scope recorded in #18697. The Breuer attribution is literature evidence, not a claim that the source conjecture was already settled. The escape registration is unfinished under #19827. The numerical experiment does not certify unsampled states or any uniform even-$n$ range. No claim is made about source results beyond the universal odd-$n$ range consequence described in Triage.
