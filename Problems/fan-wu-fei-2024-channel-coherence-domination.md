---
slug: fan-wu-fei-2024-channel-coherence-domination
bibkey: fanwufei2024channelcoherence
doi: 10.1007/s11128-024-04309-w
url: https://arxiv.org/abs/2506.10796v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result
---

# Fan–Wu–Fei channel coherence domination is false

## Problem

J. Fan, Z. Wu and S.-M. Fei, *Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy*, Quantum Information Processing 23, 100 (2024), DOI 10.1007/s11128-024-04309-w; arXiv:2506.10796v1, Section 3, page 8:

> From the examples in the next section and numerical results, it is conjectured that C_{α,1}(φ) ≥ C̃_{α,1}(φ) holds for all quantum channels φ, but we have not yet found a proof.

[Preregistration #20020](https://github.com/the-omega-institute/trureturing/issues/20020) fixes the source conventions and the settlement as Refuted. The [Library note](../Library/Divergence/fanwufei2024channelcoherence.md) gives the source locators. The parameter range is $\alpha\in(0,1)\cup(1,2]$ from Eq. (8).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Eqs. (1)–(2), $z=1$ | `renyiDiv` | The real part of the trace of the three-factor power sandwich, outer power $1/\alpha$, subtraction of one and division by $\alpha-1$ are literal. |
| Eq. (7), incoherent states on $A\times B$ | `coherence` | Infimum over positive semidefinite trace-one diagonal matrices; normalized Choi entries retain the factor $1/|A|$. |
| Eq. (9), computational-basis dephasing | Diagonal expressions inside `coherence` and `commutativityCoherence` | The public formulas inline the source expression; proofs use `ProjectedUnistochasticDynamics.projectiveReadout`. |
| Eq. (10), supremum over every input state | `commutativityCoherence` | The full positive semidefinite trace-one domain is retained. |
| Every CPTP channel between finite systems | `claim` | Finite index types with decidable equality, `MatrixMap`, complete positivity and trace preservation on every matrix. The counterexample uses two nonempty two-dimensional systems. |
| Every allowed $\alpha$ and $\widetilde C_{\alpha,1}\le C_{\alpha,1}$ | `claim` | Both intervals and the non-strict comparison are retained. |
| Refutation | `result` | The theorem proves the negation of that universal proposition, with no hypotheses. |

Finite enumerations and decidable equality implement the matrix coordinates. Matrix powers use the pinned continuous functional calculus. Density and Choi expressions are inlined literally, with private consumed correspondences to existing owners. No additional channel hypothesis restricts the conjecture.

## Motivation

The two quantities observe different aspects of a channel. The normalized Choi matrix includes both prepared outputs with equal weight; the supremum over input states can select the more coherent output. The counterexample shows that complete positivity and trace preservation alone do not impose the proposed ordering.

## Gap

The published source explicitly leaves the comparison as a conjecture. The literature screen recorded in #20020 and the supplied search evidence found no settlement in the searched material. Four citing works were enumerated through OpenAlex and Semantic Scholar; Crossref reports five citations. The fifth citation is unresolved, and the full texts of DOI 10.1140/epjd/s10053-025-00995-y and DOI 10.1088/1612-202X/ae7703 were unavailable in the retrieved pages. Completeness is ASSUMED-UNVERIFIED.

## Route

Write $\sigma_t=\tfrac12\begin{pmatrix}1&t\\t&1\end{pmatrix}$ and
$\phi(X)=X_{00}\sigma_{3/4}+X_{11}\sigma_{1/2}$.
The private declarations `phi_kraus`, `phi_cp` and `phi_tp` verify a rational sixteen-Kraus representation, complete positivity and trace preservation. Choi positivity uses the closed `FiniteKrausRepresentation.choi_PSD_iff_CP_map`; that source is reused without claiming frozen membership.

The private `choi_square` gives $\operatorname{Re}\operatorname{Tr}(M_\phi^2)=45/128$. The feasible incoherent state $I/4$ gives, through `choi_div` and `coherence_upper`,

$C_{2,1}(\phi)\le\sqrt{45/32}-1$.

The input $\rho_0=\operatorname{diag}(1,0)$ gives divergence $1/4$ by `rho0_div`. Every input state has diagonal weight $p=\operatorname{Re}\rho_{00}\in[0,1]$, and `input_div` gives divergence $\sqrt{1+(1/2+p/4)^2}-1$. The bound `input_div_le` establishes boundedness above, allowing `commutativity_lower` to conclude

$1/4\le\widetilde C_{2,1}(\phi)$.

The infimum set is nonempty and bounded below: `quarter_state` supplies its feasible point and `renyi_lower` supplies the lower bound $-1$. Since $45/32<25/16$, the square-root upper bound is strictly below $1/4$. `result` derives the contradiction.

## Falsifier

A universal comparison must hold at $A=B=\operatorname{Fin}(2)$, $\alpha=2$ and the displayed CPTP map. The certified strict separation at that instance refutes it. The Choi upper bound also uses the Choi state of the completely depolarizing channel, so restricting the feasible comparison point to that incoherent channel preserves this witness.

## Evidence

The settling declaration is `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result`. Its admission basis is `open-problem-resolution (#20020; Refuted)`; generality is `I`, and utility is `certified-instance; basis=refutes`. Every theorem is conservatively classified `bind-only`; private helpers organize applications and normalization and have consumers on the settling proof path. No escape-content claim is made.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/5a49dc2607fd5e450b26348c6119bc8f62b66584/docs/reports/fan-wu-fei-2024-channel-coherence-domination). The script is `check.py`, SHA-256 `55519b711397bd4898a996942d4c63e51292bb2c145d8cfa0bf4acb2f3f08bb1`. Command: `/opt/homebrew/bin/python3 /Users/auric/.sshx/421ef23d1783d3534dbefcce/attempt-1/experiment-check.py`; exit 0, `ALL_CHECKS True`.

The exact rational calculation gives $\operatorname{Tr}(M^2)=45/128$. Numerical readings are $D_{2,1}(M,I/4)=0.185854$, $D_{2,1}(\sigma_{3/4},I/2)=0.250000$ and the Eq. (8) value $0.184017$. The script tests phase-flip parameters $p\in\{0.2,0.7\}$ and $\alpha\in\{0.5,2\}$ against Eqs. (8) and (13), including random diagonal feasible points. It tests the fixed prepared outputs $r=3/4,s=1/2$ at $\alpha\in\{0.1,0.3,0.5,0.8,0.95,1.05,1.3,1.6,2\}$. These finite numerical checks make no uniform parameter claim.

## Triage

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Published conjecture and tier | Literature reading: Section 3 explicitly states the conjecture in Quantum Information Processing; tier 1. | Completeness of the settlement search is ASSUMED-UNVERIFIED. |
| Settlement | Proved in Lean: `result` negates `claim` at the two-dimensional witness and $\alpha=2$. | Refuted universal comparison; no exact Choi coherence is asserted. |
| Channel validity | Proved in Lean: `phi_kraus`, `phi_cp`, `phi_tp`. | Fixed prepared outputs $3/4$ and $1/2$. |
| Choi square trace | Proved in Lean: `choi_square` gives $45/128$. | This witness only. |
| Choi coherence upper bound | Proved in Lean: `coherence_upper`. | $C_{2,1}(\phi)\le\sqrt{45/32}-1$. |
| Commutator coherence lower bound | Proved in Lean: `commutativity_lower`, supported by `rho0_div` and `input_div_le`. | $1/4\le\widetilde C_{2,1}(\phi)$. |
| Strict separation | Proved in Lean: the square-root comparison in `result`. | The universal statement is false. |
| Numerical Eq. (8) value | Computed: the pinned experiment, command and SHA-256 above. | $0.184017$ is a numerical value, not an exact Lean theorem for `coherence`. |
| Source phase-flip examples | Computed: the same experiment at exactly the four $(p,\alpha)$ pairs above. | Random feasible-point checks are finite tests. |
| Other sampled orders | Computed: the same experiment at exactly the nine orders above and fixed outputs. | No uniform extension in $\alpha,r,s$. |
| All-order two-parameter family | Open as a formalization: the search-seat assertion covers $0<s<r<1$ and all allowed $\alpha$. | Neither this module nor the finite experiment proves that family. |
| Surviving channel classes | Open: classification beyond this counterexample, including general depolarizing and amplitude-damping families. | The source reports examples; this delivery proves no class theorem. |
| Proof shape and admission | `bind-only` for every theorem; the external open-problem settlement supplies admission and the helpers are consumed. | `open-problem-resolution (#20020; Refuted)`; certified refutation instance. |

### What the settlement shows

**Failure mechanism (proved in prose from the stated formulas).** At order two, the squared-trace contribution of the two Choi blocks is their average, whereas a basis-state input selects one prepared output. For the certified outputs the averaged upper bound is strictly smaller than the selectable-output lower bound. The conjecture fails within measure-and-prepare channels even with completely mixed dephased output; complete positivity and trace preservation survive.

**Nearest surviving statements.** The module proves the one-sided Choi and commutator bounds listed above. The experiment verifies the source phase-flip formulas at its four sampled points. A classification of channels satisfying domination remains open; the source's depolarizing and amplitude-damping examples are not universal class results supplied by this module.

**Consequences for the source.** The conjectured universal ordering cannot be used to compare the two quantities for arbitrary channels. Definitions and separately established examples are not contradicted by this counterexample. No source theorem is claimed to depend on the conjecture without a verified dependency, and no other source theorem is claimed refuted.

## ASSUMED-UNVERIFIED

Literature completeness, the unresolved fifth citation and the two unavailable full texts remain unverified. The unrestricted `exact?` search is not certified complete; candidate-directed applications, source-shape searches and compiled correspondences establish the stated reuse decisions. The all-order two-parameter family and the classification of surviving channel classes are outside the kernel-checked settlement. The numerical Eq. (8) evaluation is not an exact value theorem for `coherence`.
