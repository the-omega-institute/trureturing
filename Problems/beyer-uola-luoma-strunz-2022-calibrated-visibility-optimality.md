---
slug: beyer-uola-luoma-strunz-2022-calibrated-visibility-optimality
bibkey: beyer2022jointmeasurability
doi: 10.1103/PhysRevE.106.L022101
url: https://arxiv.org/abs/2111.02854
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.result
---

# Optimal calibrated visibility for joint quantum work measurements

## Problem

K. Beyer, R. Uola, K. Luoma and W. T. Strunz, *Joint measurability in
nonequilibrium quantum thermodynamics*, arXiv:2111.02854v2,
*Physical Review E* 106, L022101 (2022), p. 4, state:

> The ansatz for the effects W^U_ab in Eq. (6) is a priori not the most general one [54]. However, numerical simulations suggest that our visibility bounds are tight and we conjecture that our construction is optimal to satisfy condition (ii) for the given model Eq. (5)

The Supplemental Material repeats:

> Therefore, we conjecture that the proposed form of the joint POVM is optimal for the given noise model if one wants to satisfy the fluctuation condition (ii).

For $d\ge2$ and $0<\lambda,\gamma<1$, set
$A_a=\lambda\Pi_a+(1-\lambda)I/d$ and
$B_b=\gamma\Pi'_b+(1-\gamma)I/d$, with $B_b^U=U^\dagger B_bU$.
If every unitary admits a parent POVM satisfying the average and fluctuation
conditions, then

$$\gamma\le\frac{2\kappa}{d+2\kappa-d\kappa},\qquad
\kappa=2\sqrt{\lambda+(1-\lambda)/d}\sqrt{(1-\lambda)/d}
 +(d-2)(1-\lambda)/d.$$

The [Library note](../Library/QuantumChannels/beyer2022jointmeasurability.md)
records conditions (i)–(ii), Eq. (5), Eqs. (8)–(9), and both conjecture passages.
Issue [#16507](https://github.com/the-omega-institute/trureturing/issues/16507)
is the first-tier preregistration of the literal conventions and universal necessity statement.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Eq. (5), initial white-noise effects | `effA` | Literal scalar-weighted matrix unit plus identity |
| Eq. (5), final white-noise effects | `effB` | Literal scalar-weighted matrix unit plus identity |
| Arbitrary relative energy bases | `effBU` and unitary quantifier in `claim` | Standard matrix units with arbitrary unitary rotation cover every relative basis |
| Lüders instrument | `luders` | The positive square root is `CFC.sqrt` |
| Condition (i), all energy assignments | `AverageCondition` | All real functions on both outcome sets |
| Condition (ii), every diagonal state and outcome | `FluctuationCondition` | PSD, trace one, zero off-diagonals, and every outcome pair |
| A parent POVM for every unitary | `claim` and frozen `ConcealmentKernelNecessityRefutation.IsPOVM` | Every effect is PSD and the effects sum to identity |
| $d\ge2$ and strict visibility bounds | Binders and antecedents in `claim` | Every natural dimension and every pair of real visibilities in the source's range |
| Eqs. (8)–(9) | `kappa`, `visibilityBound`, `result` | Necessity of the literal bound |

The finite index type represents $d$ outcomes and a $d$-dimensional Hilbert
space. The universal unitary quantifier absorbs the choice of the final energy
basis. PSD and trace-one hypotheses define a density matrix; the zero-entry
hypothesis defines its diagonality. These are source conditions, not additional
restrictions on admissible parents. The public effects are literal source
expressions; the proof uses the frozen Tomiyama noise map `phi` through the
private consumed correspondence `source_effect_eq_phi`.

## Motivation

The theorem removes the restriction to the inverse-Lüders ansatz in the
necessity direction. It applies to every parent POVM, every $d\ge2$, and both
visibilities in $(0,1)$. Together with the source's sufficiency theorem, it
establishes the conjectured optimal universal visibility threshold.

## Gap

The source conjectures necessity after proving sufficiency. The literature
screen identifies no earlier proof or refutation in its searched scope;
completeness is `ASSUMED-UNVERIFIED`. The Lean statement establishes necessity;
source sufficiency and the general bistochastic extension are separate evidence.

## Route

The [Lean module](../D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality.lean)
uses `marginalB` to extract the second marginal from condition (i).
`sqrt_effA` applies `EntropyProductionCoherenceDeletionIdentity.cfc_diagonal`
to identify the positive square root of the initial diagonal effect.
`luders_single` and `diagonal_pin` specialize condition (ii) to basis states.
`had_pair_exists` applies `HaarTwoCopyTwirl.Hadamard.hadamard_unitary` and
`NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq` to obtain one
unitary with the required two-level entries. `psd_sum_coherence` applies
`CartesianVariance.psd_entry_bound` and the norm triangle inequality.
`coefficient_sum`, `kappa_identity` and `visibility_algebra` finish the bound.
All these private helpers are consumed by the proof of `result`.

## Falsifier

A counterexample to `claim` would require parameters in its exact range, a
visibility above the bound, and an admissible parent for every unitary.
The two-level Hadamard unitary forces $\gamma/2\le\kappa t$ with
$t=\gamma/2+(1-\gamma)/d$, contradicting that visibility. A parent for one
other basis, or a parent failing the fluctuation condition, is outside this
universal assertion.

## Evidence

`D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality.result`
is the kernel-checked necessity theorem. Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Blueprint records one `OpenProblemResolutionClaim` with resolution Proved.
The module's admission basis is `open-problem-resolution (#16507; Proved)`;
its proof shape is bind-only and its utility classification is `none`.

### Experiment

The independent numerical and symbolic evidence is in the
[pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f2139d44d2540e3ddf3b3294d4b36f039d0da686/docs/reports/beyer-uola-luoma-strunz-2022-calibrated-visibility-optimality).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/beyer-uola-luoma-strunz-2022-calibrated-visibility-optimality/check.py`;
exit 0, `ALL_OK`. The file matches the pinned commit and has SHA-256
`c9d7e8b2e4d948a97d897a557e9d99161d92ee213291a3a66c6aa9ca9be58363`.
The symbolic check verifies the coefficient identity and cleared-denominator
bound equivalence. The exact rational instance is $d=3$, $\lambda=1/2$,
$\gamma=4/5$: $\kappa=5/6$, $t=7/15$, $\kappa t=7/18<2/5=\gamma/2$,
and the bound is $10/13$. The float64 construction check uses $d=2,3,4,5,6$,
$\lambda\in\{0.2,0.5,0.8\}$, and 20 sampled bases per visibility and dimension
(60 per dimension, 300 total), at $\gamma$ equal to the bound. With tolerance
$10^{-10}$ it checks PSD of $C_b$, both marginals of $W_{ab}$ and the diagonal
identity. This finite numerical scope is not a uniform sufficiency proof.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Fluctuation fixes the diagonal | Proved, kernel-checked `diagonal_pin` on `result`'s proof path | Each parent entry is $(W_{ab})_{kk}=(A_a)_{kk}(B_b^U)_{kk}$ |
| PSD minors cap the parent coherence | Proved, kernel-checked `psd_sum_coherence` and `coefficient_sum` on `result`'s proof path | The summed coherence between two selected levels is at most $t\kappa$ |
| A two-level rotation forces the bound | Proved, kernel-checked `had_pair_exists` and `result` | One Hadamard pair suffices for necessity for every $d\ge2$; no mutually unbiased basis is required |
| Converse and sharpness | Proved in the source paper, Eq. (6) and Supplemental Material's inverse-Lüders construction | Source sufficiency plus Lean necessity makes the universal bound sharp; sufficiency is not formalized here |
| General bistochastic initial noise and white-noise final effects | Proved in prose below | Necessary pairwise inequality; no Lean formalization or sufficiency claim |
| General-noise sufficiency | Open | Not proved in the source; not an author-stated conjecture for this inequality; later literature completeness is unverified |
| Symbolic and rational readings | Computed by the pinned experiment, exit 0 | Exact identities and the single rational instance stated in Evidence |
| Float64 parent construction | Computed by the pinned experiment, exit 0 | Exactly the 300 sampled bases in Evidence; uniform sufficiency comes from the paper, not this computation |

The source's sufficient construction and other results retain their stated
scope. The new necessity removes the optimality conjecture's dependence on
numerical evidence. It imposes no claim that every fixed basis has this same
threshold: the universal bound is forced by a two-level rotation, and the
source's Fig. 2 compares other bases.

### General bistochastic model: prose proof

Let $R$ be a nonnegative bistochastic matrix and
$A_a=\operatorname{diag}(R_{ak})$. Keep the final white-noise effects and
both conditions. Choose the Hadamard rotation on levels 0 and 1 and final
outcome 0, so $(B_0^U)_{00}=(B_0^U)_{11}=t$ and
$(B_0^U)_{01}=\gamma/2$. Evaluating condition (ii) on each basis projector
makes $(W_{a0})_{00}=R_{a0}t$ and $(W_{a0})_{11}=R_{a1}t$.
PSD gives $|(W_{a0})_{01}|\le t\sqrt{R_{a0}R_{a1}}$.
The second marginal and the triangle inequality therefore imply

$$\frac\gamma2=\left|\sum_a(W_{a0})_{01}\right|
\le t\sum_a\sqrt{R_{a0}R_{a1}}
=\left(\frac\gamma2+\frac{1-\gamma}{d}\right)
\sum_a\sqrt{R_{a0}R_{a1}}.$$

This argument uses the same actual parent throughout. It establishes
necessity in ordinary mathematics, not a new Lean theorem. The white-noise
$R$ reduces its sum to $\kappa$. Sufficiency for arbitrary $R$ remains open
here; the source does not state this generalized inequality as its conjecture.

### Literature status: SciPost-free screen

The preregistration records the orchestrator's source and literature readings:
the arXiv v2 source and supplement, Beyer's 2023 TU Dresden thesis
*On the Measurement of Quantum Work: Operational Aspects* (qucosa 86563),
and arXiv full texts 2605.18095, 2510.04253, 2406.18632, 2403.17138,
2402.06039, 2310.11653, 2307.08405, 2212.02815, 2209.06024, 2208.13588,
2206.11783 and 2104.09364. The thesis's sections 4.5–4.6 treat the restricted
ansatz; no optimality proof is identified in the recorded screen.
The codex-cli research evidence additionally covers full texts 2607.15874,
2406.13403, 2408.13417, 2407.07711, 2402.13080 and 2112.06784, plus
post-2022 author-list searches. No matching settlement is identified there.
These are attributed prior source readings; the screen relies on arXiv and
thesis text without SciPost access. The separately listed 2026 journal
version of 2605.18095 is not independently screened. Literature completeness
and global absence of a prior settlement are `ASSUMED-UNVERIFIED`.

### Escape audit

The four-slot escape audit is unfinished for `result`, the published
`HaarTwoCopyTwirl.Hadamard.hadamard_unitary`, and the published
`NandiMutualPredictabilityLOCCRefutation.half_sqrt_two_sq`:
[#16609](https://github.com/the-omega-institute/trureturing/issues/16609).
No validated registration is claimed. The missing evidence comprises
faithful source reconstruction, lawful enrolled readouts, variation and
sensitivity proofs, actual observational dependence and compiled binding evidence.

## ASSUMED-UNVERIFIED

Literature completeness beyond the specified screen, global novelty and
publication priority are unverified. Source sufficiency is not formalized
by this module. General bistochastic sufficiency is open here. Numerical
sufficiency checks cover only the explicit tested scope. Four-slot escape
registration is unfinished and carries the linked issue; it does not alter
the kernel-checked necessity statement.
