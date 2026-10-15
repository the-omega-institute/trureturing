---
slug: utagi-banerjee-srikanth-2024-purely-nonunital-eternal-nonmarkovianity
bibkey: utagi2024eternal
doi: 10.1142/S0219749923500399
url: https://arxiv.org/abs/2203.10625
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result
---

# A rotating replacement state refutes purely non-unital eternal non-Markovianity impossibility

## Problem

S. Utagi, S. Banerjee and R. Srikanth, *On the eternal non-Markovianity of non-unital quantum channels*, arXiv:2203.10625v2, International Journal of Quantum Information 22(1), 2350039 (2024), DOI 10.1142/S0219749923500399, Section IV, conjecture:

> These diverse examples examined in the Section suggest that a purely non-unital channel (i.e., one lacking any unital component) is impossible. Although we have only studied the qubit case, we conjecture that it is true for non-unital channels in arbitrary finite dimensions.

Section V restates:

> However, we conjecture that for a non-unital channel with no such unital component (in the above sense) to be ENM, is impossible.

The source's Definition 1 attributes purely non-unital non-Markovianity to the translation in the Bloch action. [The source note](../Library/QuantumChannels/utagi2024eternal.md) gives the locators and quotations. [#16599](https://github.com/the-omega-institute/trureturing/issues/16599) fixes the complete qubit conventions and the all-positive-times criterion, without a nonzero negative asymptotic bound.

### Statement echo

| Source clause or explicit convention | Lean counterpart | Scope |
| --- | --- | --- |
| Qubit dynamics on all complex matrices | Real-time `PhyslibLeaf.MatrixMap (Fin 2) (Fin 2) ℂ` in `claim` | The qubit case suffices to refute an assertion for arbitrary finite dimensions. |
| CPTP at every nonnegative time | Existing `CoPRelativeQuantumnessRefutation.IsCPTP` in `claim` | Complete positivity and trace preservation are reused literally. |
| Dynamics starts at the identity | Identity hypothesis in `claim` | Required on every matrix, not only states. |
| Eqs. (9)–(11): delete the translation | `unitalPart` | Its complete body is the preregistered subtraction $\Phi_t(X)-\operatorname{Tr}(X)(\Phi_t(I)-I)/2$. |
| Definition 1: translation alone supplies non-Markovianity | `PurelyNonUnital` | Non-unital at every positive time; the unital part has a CPTP intermediate map for every $0\le s\le t$. |
| Time-local generator | `IsGeneratorAt` | Entrywise real-time derivative on every complex matrix. |
| Conditional complete positivity | `CondCP` | The existing output-first `MatrixMap.choi_matrix` is tested on every trace-free vector. |
| Negative generator direction at every $t>0$ | `EternallyNonMarkovian` | No negative asymptotic bound is asserted. |
| Impossibility conjecture | `claim`, negated by `result` | Every quantifier and hypothesis above is retained. |

The entrywise derivative and conditional-Choi criterion are the explicit mathematical conventions of #16599. They do not restrict inputs to density matrices or replace the source's unital part by a certificate predicate.

## Motivation

`D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result` refutes the literal qubit claim. It identifies a rotating replacement state as a mechanism by which a divisible isotropic contraction coexists with a generator that fails conditional complete positivity at every positive time.

## Gap

The conjecture extrapolates from restricted examples to all non-unital channels. A rotating replacement direction falls outside the fixed-axis examples. The preregistration's eight citing works were screened by the orchestrator; the additional literature screen in the independently supplied evidence includes Jagadish–Srikanth's fixed-axis result. No settlement was found in that searched scope. Completeness of the literature screen is not established.

## Route

Put $D_t=1+t^2$, $P_t=\begin{pmatrix}1&t\\t&t^2\end{pmatrix}/D_t$ and
$\Phi_t(X)=(X+t^2\operatorname{Tr}(X)P_t)/D_t$.

1. The private `kraus_action`, `phi_trace` and `phi_cptp` prove that the four explicit Kraus matrices give a CPTP family. `phi_zero` gives the identity at zero; `phi_nonunital` gives non-unitality for every positive time.
2. `unital_formula` identifies the isotropic unital part. `dep_cptp` applies the published frozen `PauliThreeWeightBayesianInverseUniqueness.channel_cptp` to four normalized nonnegative weights. `dep_intermediate` and `phi_purely` prove its divisibility with parameter $(1+s^2)/(1+t^2)$.
3. `inverse_pair`, `generator_composition`, `rational_deriv` and `phi_generator` give the exact inverse and entrywise generator. The trace-free vector in `v_trace` has conditional Choi form $-2t^3(1+t^2)(t^2+4)$ by `v_form`. `l_not_condcp` and `phi_eternal` prove strict failure at every $t>0$.
4. `result` applies this family to the universal `claim` and obtains a contradiction.

These are consumed private proofs, not extra public assertions. The proof shapes are bind-only after expansion into frozen Kraus facts, pinned derivative rules and normalization; admission is `open-problem-resolution (#16599; Refuted)`.

## Falsifier

The settlement would fail if any nonnegative-time map were not CPTP, if the unital part lacked the required CPTP intermediate, if the proposed generator did not differentiate the dynamics, or if its conditional Choi form were nonnegative at some positive time. The exact kernel-checked constructions discharge all four obligations. The finite numerical rate checks alone do not discharge the last universal obligation.

## Evidence

The Lean module and [its Blueprint](../Blueprint/D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.md) supply the exact refutation. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

### Experiment

[The independent symbolic and numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/04e546b1348ed5c1100b3c7235cb818b68e57eeb/docs/reports/utagi-banerjee-srikanth-2023-purely-nonunital-eternal-nonmarkovianity), pinned to `04e546b1348ed5c1100b3c7235cb818b68e57eeb`, contains `check.py`, SHA-256 `4f50382c098973a0e11a88db2110ef49338acac811a05f2c80bcd711c22e8e23`. Command: `python3 check.py` in that pinned directory; exit 0, `ALL_OK`.

Its exact symbolic checks cover the Kraus action/completeness, identity at zero, non-unitality, the unital-part formula and intermediate composition, the inverse, and the finite intermediate quadratic-form identity $-s^2(t-s)^2/((1+s^2)(1+t^2))$. Its 40-digit numerical comparison of the minimum conditional Choi eigenvalue with $(t/D_t)(1-\sqrt{1+t^2/D_t^2})$ tests exactly $t\in\{1/10,1/2,1,2,5\}$, giving respectively $-0.000484111535869057$, $-0.0308131845707603$, $-0.0590169943749474$, $-0.0308131845707603$ and $-0.00352370258688945$. The eigenvalue formula is not a Lean theorem in this module.

### Escape audit

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The published owner `PauliThreeWeightBayesianInverseUniqueness.channel_cptp` has an unfinished four-slot escape audit under [#16744](https://github.com/the-omega-institute/trureturing/issues/16744). A complete CPTP-family realization, equivalence bridge, variation/sensitivity evidence and enrolled readout are missing; no validated Reg registration is claimed.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Channel family and identity initial condition | Proved, kernel-checked: `phi_cptp`, `phi_zero`, consumed by `result` | All nonnegative times; all complex qubit matrices. |
| Non-unitality and Markovian isotropic contraction | Proved, kernel-checked: `phi_nonunital`, `unital_formula`, `dep_intermediate`, `phi_purely` | Non-unital for every positive time; a CPTP unital intermediate for every $0\le s\le t$. |
| Generator's eternal negative direction | Proved, kernel-checked: `phi_generator`, `v_trace`, `v_form`, `l_not_condcp`, `phi_eternal` | The trace-free conditional Choi form is strictly negative for every $t>0$. |
| Tangential translation mechanism | Proved in prose by the derivation below | Rotation creates translation velocity whose norm exceeds the isotropic contraction rate. The kernel proof of the same obstruction uses the conditional Choi vector, not this Bloch-norm identity. |
| Source's Theorems 1–2 for GAD channels | Published literature result: Utagi–Banerjee–Srikanth, Theorems 1–2 | Their restricted GAD conclusions survive; this family is outside that fixed-axis class. |
| Fixed-axis surviving boundary | Published literature result: Jagadish–Srikanth, Theorem 2 | For their Eq. (15), the non-unital decay rate cannot have a strictly negative asymptotic bound. |
| Fixed axis and scope of the no-go | Proved in prose from the explicit replacement direction; literature boundary as above | The counterexample rotates, so the fixed-axis hypothesis is essential to applying that no-go to it. This does not claim that removing only that hypothesis refutes the stronger asymptotic statement. |
| Finite intermediate form and sampled canonical rates | Computed by the pinned experiment above, exit 0 | Exact symbolic intermediate identity; numerical eigenvalue comparison only at the five listed times. |
| Existence of analogous purely non-unital ENM dynamics in dimension $d\ge3$ | Open | The qubit result refutes the universal conjecture but constructs no higher-dimensional family. |
| Whether purely non-unital ENM requires a rotating fixed point | Open | The construction is sufficient; no necessity classification is supplied. |
| Consequences for source results using the conjecture | Literature boundary | The conjectural impossibility is refuted under #16599's weak ENM criterion. The source's proved GAD Theorems 1–2 and its other explicit examples are not invalidated. |

For the mechanism, the replacement Bloch direction is
$n_t=(2t/D_t,0,(1-t^2)/D_t)$, with $\|n_t\|=1$, $n_t\cdot\dot n_t=0$ and $\|\dot n_t\|=2/D_t$ by differentiating its coordinates. Write $\lambda_t=1/D_t$, $\tau_t=(1-\lambda_t)n_t$ and $a_t=-\dot\lambda_t/\lambda_t=2t/D_t$. The affine Bloch generator is $\dot r=-a_t r+b_t$, where
$b_t=\dot\tau_t+a_t\tau_t=a_t n_t+(t^2/D_t)\dot n_t$. Orthogonality gives
$\|b_t\|^2=a_t^2+4t^4/D_t^4>a_t^2$ for $t>0$. The tangential term is nonzero at every positive time while the scalar contraction is a divisible depolarization. These displayed identities are the prose derivation; `v_form` and `phi_eternal` are its kernel-checked conditional-Choi counterpart.

V. Jagadish and R. Srikanth, *Eternal non-Markovianity of qubit maps*, [arXiv:2501.06846v2](https://arxiv.org/abs/2501.06846v2), Physical Review A 111, 042212 (2025), [DOI 10.1103/PhysRevA.111.042212](https://doi.org/10.1103/PhysRevA.111.042212), Theorem 2, concerns the fixed-axis map of Eq. (15) and excludes a non-unital rate bounded away from zero on the negative side asymptotically. Remark 3 expressly leaves weak quasi-eternal negativity tending to zero. This is a surviving published boundary, not a theorem proved or imported by this module.

## ASSUMED-UNVERIFIED

Literature completeness beyond the screened sources is ASSUMED-UNVERIFIED. The source and citation screen recorded in #16599 is orchestrator-reported evidence; the additional paper readings in the supplied envelope are seat-reported. Equivalence to alternative stronger definitions of eternal non-Markovianity, microscopic system–bath realization, higher-dimensional constructions and necessity of rotation are not established here. The escape audit in #16744 is unfinished.
