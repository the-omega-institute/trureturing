---
slug: stasiuk-lutkenhaus-tan-error-state-erasure
bibkey: stasiuklutkenhaustan2025erasure
doi: 10.1103/PhysRevA.111.022631
url: https://arxiv.org/abs/2212.06975v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.result
---

# Stasiuk–Lütkenhaus–Tan's operational error-state erasure conjecture

## Problem

Stasiuk, Lütkenhaus and Tan, arXiv:2212.06975v3, Section III A, p. 5, immediately after Theorem 2, write:

> We remark that it does seem plausible to conjecture that Eve can indeed always perform an operation on her side-information such that this condition is fulfilled (while keeping the states $\rho_{ET|00},\rho_{ET|11}$ unchanged), because it essentially corresponds to having Eve “erase” her side-information whenever Alice and Bob did not get the same output value.

The [source note](../Library/Entropy/stasiuklutkenhaustan2025erasure.md) locates equation (6) and the conjecture. [Preregistration #24328](https://github.com/the-omega-institute/trureturing/issues/24328) fixes the operational interpretation: one CPTP channel on the full joint system $ET$, fixing the two correct states separately and identifying the two error outputs. The universal operational claim is **Refuted** by `D5.S3.Quantum.Foundation.StasiukLutkenhausTanErrorStateErasureRefutation.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (6), equal public-bit weights and complemented outcomes | `rhoET` | Literal entrywise matrix, including both flag coordinates and the factor $1/2$ |
| Eve's conditional states | `sigma : Bool → Bool → DensityState (Fin d)` in `claim` | Four normalized states, with no purity or distinguishability hypothesis |
| Eve can always perform an operation | Universal `d` and `sigma`, then one existential `QuantumChannel` in `claim` | Every finite dimension; arbitrary joint CPTP action on $ET$ |
| Keep $\rho_{ET\mid 00}$ and $\rho_{ET\mid 11}$ unchanged | First and second equalities of `ErasesErrorsPreservingCorrect` | Separate exact preservation |
| Fulfil $\rho_{ET\mid 01}=\rho_{ET\mid 10}$ by the operation | Third equality of `ErasesErrorsPreservingCorrect` | Equality of the two channel outputs |
| Refutation | `result : ¬ claim` | The positive source assertion is negated without dropping the public flag |

`DensityState` and `QuantumChannel` are reused from `FiniteStateChannel`. The public definitions retain the preregistered expressions; proofs use `Matrix.vecMulVec` and `Pi.single` directly. The namespace follows the delivered file. Arbitrary finite ensembles are physically realizable: purify each conditional state on $F\otimes E$ with $F$ assigned to Alice, attach the two key bits, and take the equal-amplitude superposition of the four orthogonal key-bit branches. Measuring those bits yields the four states with probability $1/4$. This is a prose realization argument, not an additional Lean theorem. The fixed physical experiment below uses balanced positive probabilities. No calculation of unbalanced posterior flag weights is asserted.

## Motivation

The operational conjecture would remove the extra equal-error-state hypothesis from the necessity discussion following Theorem 2. Its failure identifies a disturbance obstruction; it does not refute that theorem or characterize all replacement attacks with the same observed correlations.

## Gap

The conjectured channel must satisfy all three equalities simultaneously. A public flip bit does not provide an orthogonal record separating correct and error events. The counterexample retains the full flag and permits coherent joint operations, so discarding the flag or restricting the channel is unnecessary.

## Route

The private witness uses real unit vectors

$$
v_{00}=(1,0),\quad v_{01}=(9999/10001,200/10001),\quad
v_{10}=(29197/50005,40596/50005),\quad v_{11}=(3/5,4/5).
$$

Let $\tau_0,\tau_1$ be their correct flagged density states and $\eta_0,\eta_1$ the error flagged states. The private `correct_distance` and `perturbation_distance` establish

$$
D(\tau_0,\tau_1)=4/5,\qquad D(\tau_i,\eta_i)=200/10001.
$$

The imported `FiniteTraceDistance.traceDistance_triangle`, `traceDistance_contract` and `traceDistance_symm` are used by the private `disturbance_bound`. For every joint CPTP channel $\Lambda$, triangle inequalities along $\tau_0,\Lambda\tau_0,\Lambda\eta_0,\Lambda\eta_1,\Lambda\tau_1,\tau_1$ and contraction on the two short legs give

$$
D(\tau_0,\Lambda\tau_0)+D(\tau_1,\Lambda\tau_1)+D(\Lambda\eta_0,\Lambda\eta_1)
\ge 4/5-400/10001=38004/50005>0.
$$

Exact preservation and exact erasure make the left side zero, yielding `result`. All proof steps are classified `bind-only`; the module's admission basis is `open-problem-resolution (#24328; Refuted)`. This asserts the external named settlement, not a new general trace-distance inequality.

## Falsifier

A CPTP channel satisfying the three displayed exact requirements for this same ensemble would contradict the compiled `result`. A source interpretation requiring only a different replacement attack does not have those requirements and is outside this refutation. The physical preparation, Bell and Chernoff claims are independently computed evidence, not hypotheses or additional conclusions of `result`.

## Evidence

The mathematical source is [the Lean module](../D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.lean), with its [Blueprint](../Blueprint/D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.md). Its public surface has three definitions and one theorem. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The [exact experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/51b0a8ca879c21213e46ef2e27b1a4682b6c13e0/docs/reports/slt-qkd-error-state-erasure) contains `check.py` at immutable commit `51b0a8ca879c21213e46ef2e27b1a4682b6c13e0`. The commit object and script were read from the local experiments clone. Command: `python3 /Users/auric/.sshx/ced3b59da98c5fd7b3dd731e/attempt-1/check.py`, exit 0; script SHA-256 `fc7e9b33a18dfd1169b3a7ea1318f36414f40f7abde12c0658a93717e0398e6f`. This is an extracted copy of that immutable script. It checks symbolic family normalization, squared pure-state distances and the CHSH identity under the unit-circle relations, and the nominated rational instance's exact matrix spectra. The source's Lemma 1 equivalence is checked only for public messages of lengths 1, 2 and 3.

## Triage

### What the settlement shows

| Item | Status and evidence | Scope |
| --- | --- | --- |
| Universal operational erasure | **Proved in Lean:** public `result` | Failure already at Eve dimension two, retaining the full public bit and allowing every joint CPTP channel |
| Disturbance mechanism | **Proved in Lean:** private `disturbance_bound`, consumed by `result` | Sum of both correct-state disturbances and residual error distinguishability is at least $38004/50005$ |
| Coincident error outputs | **Proved in prose from `disturbance_bound`:** substitute equal error outputs; their trace distance is zero | The two correct-state disturbances sum to at least $38004/50005$; no additional public theorem is claimed |
| Physical and symbolic checks | **Computed:** immutable experiment entry above, exit 0 | Four distinct flagged states; normalized three-qubit preparation; positive balanced key-event probabilities; $Q=9/25<9/16$; $\mathrm{CHSH}=12498946\sqrt{34}/31253125>2$; symbolic family identities under the stated unit-circle relations; Lemma 1 messages of lengths 1–3 |
| Positive key rate, Theorem 2 and replacement attacks | **Open here** | No positive key rate or replacement-attack realization theorem; Theorem 2 retains its equal-error-state hypothesis and is not refuted |
| Extensions and sharpness | **Open here** | Full Lean parameter family, optimal disturbance constant, and restricted positive erasure with an orthogonal correct/error record |
| Neighbouring asymptotic results | **Open here:** finite-blocklength security and replacement realization | Bhavsar–Moon–Bae, arXiv:2602.05870v2, studies neighbouring asymptotic key-rate conditions; finite-blocklength security and replacement realization require separate evaluation |

The approximate-erasure obstruction follows quantitatively from the displayed inequality. An orthogonal correct/error record is a candidate additional hypothesis for selective erasure; this delivery supplies no general positive theorem under that hypothesis. Neither this finite matrix refutation nor the experiment settles finite-blocklength security.

## ASSUMED-UNVERIFIED

Literature completeness is **ASSUMED-UNVERIFIED**. The source and literature screen are recorded in #24328; the additional accessible screen in the supplied research envelope includes Bhavsar–Moon–Bae arXiv:2602.05870v2. No screened accessible source supplied this operational settlement. The second OpenAlex citation remains unidentified, Jha–Hati's subscription full text is unread, general web full-text search was unavailable, and equality of the final PRA body with arXiv v3 is unverified. These limits do not certify novelty. Physical realization and Bell/Chernoff family identities are prose or exact-computation evidence; the formal claim is precisely the finite-state operational refutation.
