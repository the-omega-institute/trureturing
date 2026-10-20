---
slug: badhani-das-2026-noisy-unitary-conditional-min-entropy
bibkey: badhani2026conditionalchannel
doi: 10.48550/arXiv.2604.01217
url: https://arxiv.org/abs/2604.01217v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.result
---

# Badhani–Das noisy-unitary conditional min-entropy

## Problem

H. Badhani and S. Das, *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*, arXiv:2604.01217v2, Section VI.1, conjecture after Proposition 10:

> We conjecture that Proposition 10 can be extended to all unitaries with added white noise. We leave this as an open problem.

Proposition 10 assumes $|B'|=|B|=2$. The statement here retains that hypothesis and takes $A'=A=\mathbb C^d$, for every positive natural $d$. For every unitary $U$ on $\mathbb C^d\otimes\mathbb C^2$ and every $p\in[0,1]$, put $N_p(Z)=p\operatorname{tr}(Z)I/(2d)+(1-p)UZU^\dagger$. Then

$$
S_\infty[A\mid B]_{N_p}=S_\infty(R_AA\mid R_BB)_{\Phi^{N_p}}-\log_2 d.
$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Arbitrary positive input/output dimension on A | The natural dimension and positivity binder in `claim` | No upper bound on $d$. |
| Qubit input/output conditioning | `Matrix.unitaryGroup (Fin d × Fin 2) ℂ` | Both B systems have dimension two. |
| Arbitrary unitary channel | The universally quantified unitary in `claim` | No selected matrix or spectrum. |
| Added white noise | `noisyUnitary` | Literal replacement-plus-unitary expression. |
| $p\in[0,1]$ | The two real inequalities in `claim` | Both endpoints included. |
| Choi operator/state | `choiN`, `choiState` | Index order $(R_A,A),(R_B,B)$, normalization $1/(2d)$. |
| State/channel conditional entropy | `condMinEntropy`, `channelCondMinEntropy` | Density states and quantum channels range over the existing repository carriers. The channel formula inlines its matrix-unit Choi expression. |
| Subtract $\log|A'|$ | The base-two logarithm term in `claim` | $|A'|=d$. |
| Universal equality | `result` | Full claim, without additional hypotheses. |

The public definitions retain the expressions prescribed in [#19060](https://github.com/the-omega-institute/trureturing/issues/19060). `Dmax` uses the real logarithm followed by coercion to `EReal`; at zero input it gives zero rather than an extended logarithm of zero. The settlement uses trace-one states and positive lower bounds on feasible costs, so that zero-input extension is outside its entropy-scaling argument.

## Motivation

This is a tier-one published conjecture. The settling GID is `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.result`, admitted as `open-problem-resolution (#19060; Proved)`. No digestion atom is used. The source note is `Library/Entropy/badhani2026conditionalchannel.md`.

## Gap

The literature screen recorded in #19060 reads the source v2, its two citing works arXiv:2510.23731v2 and arXiv:2506.24079v3, and precursor arXiv:2410.01740; neither citing work supplies this conjecture's proof. Searches cover the title and authors, arXiv conditional-channel-entropy results, MathDB, the pinned formal-conjectures register, and repository issues and problem dossiers. No settlement was found in that searched scope. Completeness is `ASSUMED-UNVERIFIED`.

## Route

The normalized reduced Choi matrix has two maximally mixed qubit marginals. In the magic basis it is real symmetric. A real spectral basis therefore becomes a maximally entangled eigenbasis. Each diagonal sign symmetry has a unitary partner on the other factor; their tensor products preserve both the pure Choi vector and white noise.

Averaging a feasible density-state optimizer over these signs pinches it in that eigenbasis and preserves its trace. Its maximally entangled eigenvectors make the pinched density matrix the normalized Choi matrix of a channel. The two entropy optimizations consequently have equal costs after the dimension scaling. Positive trace bounds justify the logarithmic scaling.

The private declarations `maximally_entangled_eigenbasis`, `sign_symmetry_of_eigenbasis`, `replacement_of_sign_symmetry` and `entropy_identity_of_sign_symmetry` supply these steps on `result`'s proof path. They are consumed helpers under the declared bind-only classification; they are not independent escape witnesses.

## Falsifier

A positive dimension, unitary and noise weight in the specified interval violating the displayed equality would refute the mathematical claim. A statement mismatch, an additional unaccounted hypothesis, or an axiom outside the standard closure would invalidate this formal settlement.

## Evidence

The Lean module is `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.lean`; its only public theorem is `D5.S3.Quantum.Information.BadhaniDasNoisyUnitary.result`. Its Scribe displays the complete expanded claim and records one `OpenProblemResolutionClaim` of kind `Proved`.

The escape audit is unfinished for that theorem: [#19176](https://github.com/the-omega-institute/trureturing/issues/19176). No successful four-slot registration is claimed. The missing evidence is a faithful dependent dimension/unitary/noise realization, the guarded source reconstruction, lawful enrolled-template readout and variation/source-selection proofs. The public owner theorems `D5.S3.Quantum.Subentropy.PinchingGap.sign_unitary` and `D5.S3.Quantum.Subentropy.PinchingGap.signTwirl_eq_blockPinch` are also unfinished audit targets under that issue: the finite coordinate/sign/matrix family requires a faithful realization, lawful enrolled-template readout, and compiled selection and variation evidence. Both statements have complete formulas in the owner Scribe. The noisy-unitary proof applies these owners after transporting four coordinates to four singleton blocks.

### Experiment

[Experiment at commit `5ceac7c1a27dc65493859cc5b5bad0056ad11a83`](https://github.com/the-omega-institute/trureturing-experiments/tree/5ceac7c1a27dc65493859cc5b5bad0056ad11a83/docs/reports/badhani-das-2026-noisy-unitary-conditional-min-entropy). Portable command from the pinned directory: `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 check.py` (NumPy, SciPy, CVXPY, CLARABEL and SCS). The pinned `check.py` has SHA-256 `0842460a7bb8242a35c320ffb4873103ba748b03cfe1554bd08a5cb4d3ce6c03`. Command: `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 /tmp/op-venv-sdp/bin/python /Users/auric/.sshx/73582a25b745cd1f643f181c/attempt-1/check.py`, run on the byte-identical pinned script; exit 0, `RESULT PASS`. The solver emitted a solution-accuracy warning. There are 48 random noisy-unitary cases ($d=1,2,3$, four unitaries each, $p\in\{0,0.25,0.6,1\}$), nine named-unitary cases (CNOT, SWAP and identity at $p\in\{0,0.5,0.9\}$), and 20 magic-basis tests ($d=1,2,3,4$, five unitaries each). Random-channel and pure-replacement controls at $d=2$ give cost gaps between 0.004522 and 0.154180; the corresponding $d=1$ controls are numerically zero. These are approximate SDP readings.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Noisy-unitary equality | Proved in Lean by `result` | Every $d\ge1$, every unitary and every $p\in[0,1]$; includes $d=1$ and both noise endpoints. |
| Decisive mechanism | Kernel-checked: `maximally_entangled_eigenbasis`, `sign_symmetry_of_eigenbasis`, `replacement_of_sign_symmetry`, `entropy_identity_of_sign_symmetry` | Maximally entangled eigenbasis, joint sign symmetry, pinching to a channel Choi state, and dimension scaling. |
| Escape witness classification | Open, no independent witness claimed | `mixed_unitary_choi`, `eigenbasis_sign_partner` and `symmetry_pinching_feasible` are consumed bind-only helpers in this delivery; admission uses the external-problem exception. |
| Computational utility | None | Symbolic unbounded dimension and arbitrary complex unitary/real noise; finite polynomial identities are normalization steps, not certified finite instances. |
| Numerical equality checks | Computed by the pinned experiment: 48 random cases and nine named-unitary cases pass | Numerical support only; not a uniform theorem. |
| Magic-basis structural checks | Computed by the pinned experiment: 20 structural tests pass | Numerical support for the tested instances only. |
| General CPTP maps and pure replacement noise | Computed by the pinned experiment: four random CPTP controls and one pure-replacement control at $d=2$ have positive gaps, ranging from 0.004522 to 0.154180 | These computed controls show failure outside the white-noise family; no exact counterexample is kernel-certified here. |
| Mixtures $0.6U_1+0.4U_2$ | Open as an independently reproduced computation in this delivery | #19060 reports five failures with $d=2$; the pinned experiment does not contain that test, so those sample counts are not certified by the reproduced program. |
| Depolarization on B alone | Open | #19060 reports six numerical agreements at $p=1/2$, $d=1,2$; the pinned experiment does not contain this test. No family theorem is inferred. |
| Larger conditioning systems | Open | The maximally entangled eigenbasis argument uses qubits; conditioning dimension greater than two is not settled. |
| Sharpness and source consequences | Kernel-checked equality: `result`; the comparison with Proposition 1 is a prose consequence | The source's general-channel upper bound is attained throughout the specified white-noise unitary family. Applications needing precisely this equality can use it. The source's other channel questions are not settled. |
| Independent verification | Open beyond bounded independent formula, helper-consumption and reuse checks | The independent codex-cli mirror assessment approves the source and mirror; verification does not certify exhaustive literature or reuse completeness. |
| Literature status | Open as an exhaustive completeness claim | The bounded screen found no settlement; completeness is `ASSUMED-UNVERIFIED`. |
| Four-slot escape audit | Open, #19176 | No `declared_validated` registration. |

## ASSUMED-UNVERIFIED

Literature-search completeness and novelty beyond the recorded search scope are unverified. Numerical solver results are approximate and do not establish exact counterexamples or uniform extensions. The zero-input extension of `Dmax` differs from an extended logarithm at zero; the settlement's trace-one bounds exclude that input. Bounded reuse searches do not prove exhaustive nonexistence of an upstream owner. Larger conditioning dimensions and the local-depolarization family remain open.
