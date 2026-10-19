---
slug: nuradha-mishra-leditzky-wilde-measured-fidelity-gap
bibkey: nuradha2025multivariate
doi: 10.1088/1751-8121/adc645
url: https://arxiv.org/abs/2404.16101v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.result
---

# A strict gap between measured and Uhlmann average fidelities

## Problem

T. Nuradha, H. K. Mishra, F. Leditzky and M. M. Wilde, *Multivariate fidelities*, arXiv:2404.16101v3, Remark 5.45, page 34, ask:

> Furthermore, it is interesting to determine whether there exists a tuple of states for which F_M(ρ_1, …, ρ_r) > F_U(ρ_1, …, ρ_r)—we leave this as an open question.

The answer is affirmative. For the three qubit states $R=I/2$, $A=(I+Z/2)/2=\operatorname{diag}(3/4,1/4)$ and $B=(I+X/2)/2$, the proof gives $F_U(R,A,B)<24/25\le F_M(R,A,B)$. Here $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$, $F_U$ is the average over unordered pairs, and $F_M$ takes one infimum over all finite POVMs of every outcome size.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Proposition 3.1: root fidelity | `uhlmann` | The existing trace norm applied to the product of positive square roots. |
| Equation (5.13): average over unordered pairs | `FU` | Real normalization $2/(r(r-1))$ and `Finset.Ioi`. |
| Definition 5.40: the measurement channel | The two diagonal trace expressions in `FM` | The literal measurement expression is inlined; no second channel definition. |
| Infimum over finite POVMs of every size | The dependent-sum index in `FM` | A single real infimum over size and POVM together; empty outcome sizes do not supply artificial zero costs. |
| Existence of a tuple with strict inequality | `claim`, `result` | Natural dimensions and tuple sizes and positive trace-one matrix states; witness dimension two and tuple size three. |

The public definition bodies are the binding expressions of [#19068](https://github.com/the-omega-institute/trureturing/issues/19068), with the measurement action expanded. No hypothesis is added to the existential question.

## Motivation

The settling GID is `D5/S3/Quantum/Information/NMLWMeasuredFidelitySeparation.result`, with `admission_basis: open-problem-resolution (#19068; Proved)`. This external named question has no digestion atom. One `OpenProblemResolutionClaim` records `Proved` on the settling declaration. The [source note](../Library/Quantum/nuradha2025multivariate.md) is the existing owner of the paper's DOI.

## Gap

Proposition 5.44 establishes $F_M\ge F_U$. Remark 5.45 asks whether strict inequality is possible. Pairwise minimization permits a different measurement for each pair, whereas the measured multivariate quantity uses a common measurement for the whole tuple.

## Route

The following private helpers belong to `D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation`.

1. `effect_coordinates` expresses a positive qubit effect using $a=\operatorname{Re}\operatorname{Tr}(E)/2$ and its two Bloch half-coordinates $b,c$, with $a\ge0$ and $b^2+c^2\le a^2$.
2. `polynomial_certificate` and `disc_inequality` establish the affine lower bound
   $\frac12(\sqrt{1+u/2}+\sqrt{1+w/2}+\sqrt{(1+u/2)(1+w/2)})\ge36/25+(53/200)(u+w)$ on $u^2+w^2\le1$.
3. `scalar_effect_bound` and `effect_lower_bound` scale this estimate to arbitrary positive effects. `uhlmann_diagonal` identifies the classical measured fidelity. `povm_pair_sum_bound` sums the estimates over any finite POVM: the scalar coefficients sum to one and both Bloch coefficients sum to zero. Thus `FM_witness_ge` gives $F_M\ge24/25$.
4. `traceNorm_sq_two` applies the existing `D5.S3.Quantum.Schatten.TraceNorm.transitionMass_sq`. `gram_root_trace` applies the published `D5.S3.QuantumStates.GNSZeroPropagation.cross_trace_factorization`. Together they give the two-by-two fidelity square formula. `qubit_fidelity_squares` and `FU_witness_lt` give $F_U<24/25$.
5. `result` supplies the three states and combines the strict upper and universal lower bounds.

All new theorem proofs are classified `bind-only`, with no escape witness claimed. Their live consumers are the subsequent helpers and `result`; the settling conclusion uses the external open-problem-resolution basis. No standalone supporting identity module is introduced. The existing public `transitionMass_sq` is reused, and the existing GNS factorization is published with its statement and proof unchanged.

## Falsifier

A failure of the disc estimate at a point of the unit disc, or $F_U\ge24/25$ for the displayed tuple, would invalidate this separation argument. The compiled helpers prove the disc estimate and the opposite strict upper bound. Numerical sampling alone supplies neither universal bound.

## Evidence

The kernel-checked settling theorem is `D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.result`. Its only public conclusion is the existential claim. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit is unfinished under [#19175](https://github.com/the-omega-institute/trureturing/issues/19175). Its targets are `D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation.result` and the published owner `D5.S3.QuantumStates.GNSZeroPropagation.cross_trace_factorization`. No Reg mirror or `declared_validated` registration is asserted. Complete source reconstruction, the exact occurrence bridge, lawful enrolled-template readout and E1–E8 evidence for these source telescopes remain required.

### Numerical experiment

[Experiment directory at `d7fb6a4a852d1e3b65208517fd568a9281bf39c5`](https://github.com/the-omega-institute/trureturing-experiments/tree/d7fb6a4a852d1e3b65208517fd568a9281bf39c5/docs/reports/nuradha-mishra-leditzky-wilde-2025-remark545-measured-fidelity-gap). The pinned `check.py` has SHA-256 `ed85e95371c3fdb0f8ec9f76b2e044f72a13155761ef061d76c99f7b59baf020`.

The rerun command is `OPENBLAS_NUM_THREADS=1 /Users/auric/.sshx/426f6ae07a7e7c82e9131836/attempt-1/venv/bin/python /Users/auric/.sshx/426f6ae07a7e7c82e9131836/attempt-1/experiment-check.py` (exit 0, `RESULT PASS`). This temporary file is byte-identical to the pinned `check.py`; the portable command is `OPENBLAS_NUM_THREADS=1 python3 check.py` from the pinned directory with NumPy and SciPy installed. The computed trace-norm value is $F_U=0.955755333091$, agreeing with $(2\sqrt6+2\sqrt2+\sqrt{14})/12$. The LP over 40006 rank-one Bloch directions gives the upper estimate $F_M\le0.967624313794$. The certificate $y_0=36/25$, $y_1=53/200$ has minimum grid slack $0.01142813$ on the $2001\times4001$ spherical grid, exceeding the stated Lipschitz margin $0.001421723$. The resulting numerical certificate lower bound is $0.96$, exceeding $F_U$ by $0.004244667$.

The tested parameter scope is exactly $a=b=1/2$ in $A=(I+aZ)/2$, $B=(I+bX)/2$. The LP optimizes over its finite direction set and gives an upper bound on the unrestricted infimum, not an exact optimum. The grid and floating-point computation are numerical evidence; the universal lower bound is separately proved by the analytic Lean argument.

## Triage

### What the settlement shows

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Mathematics | Proved, kernel-checked: `result` | The unchanged existential claim, with the single-index `FM`, holds for the displayed three qubits. |
| Production | Proved, kernel-checked applications in `traceNorm_sq_two` and `gram_root_trace` | One settling module reuses the existing public `transitionMass_sq` and publishes the original GNS factorization. There is no new standalone identity module. |
| Proposed escape witnesses | Open, no escape witness asserted | `polynomial_certificate`, `disc_inequality` and `povm_pair_sum_bound` are consumed `bind-only` helpers. No escape witness is claimed; the settling module's admission basis is the named external open question. |
| Escape audit | Open, missing registration evidence | Both public targets are listed in #19175. Scribe delivery and freezing do not certify escape registration. |
| Decisive mechanism and extent | Proved, kernel-checked: `disc_inequality`, `povm_pair_sum_bound`, `FM_witness_ge` | An affine disc estimate survives summation over every finite POVM of every size. No restriction to projective, two-outcome or rank-one measurements is imposed. |
| Incompatible pairwise optima | Proved in prose from the separation and source Proposition 3.1 | If one POVM reached all three pairwise minima, its sum would equal $3F_U$ and force $F_M\le F_U$, contradicting the separation. Thus no such common POVM exists for this tuple. This argument asserts no general converse or attainment theorem. |
| Gap at $a=b=1/2$ | Computed: the pinned experiment above | The trace-norm value, finite-direction LP upper estimate and certificate grid check have exactly the scope reported above. The analytic lower bound is independently proved in Lean. |
| Gaps at $a=b=0.9$ and $(a,b)=(0.3,0.7)$ | Open here | The approximate values in #19068 are not reproduced by the pinned program, which fixes $a=b=1/2$; no claim about these other parameters is certified by this delivery. |
| Equality classification by commuting transports | Open | The proposed criterion for full-rank anchors is neither proved nor numerically checked here. |
| Uniform quantitative family bound | Open | The proposed bound involving $\min\{a^2/(1+a)^{3/2},b^2/(1+b)^{3/2}\}/24$ is not established. |
| Sharpness and exact measured value | Open | The proof supplies $F_M\ge24/25$; it does not identify the optimum, prove sharpness or classify equality for arbitrary tuples. |
| Literature | Open, literature reading recorded in #19068; completeness `ASSUMED-UNVERIFIED` | The source explicitly leaves Remark 5.45 open. The recorded screen found no answer among the works examined. |

Proposition 5.44 retains its stated comparison. The result shows that its inequality can be strict; it does not change the hypotheses or conclusions of the source's other fidelity results. No further source theorem is claimed to depend on an affirmative answer to Remark 5.45.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen in #19068 read arXiv:2404.16101v3, Sections 3 and 5.5, searched the measured-multivariate-fidelity terminology, and examined seventeen citing or nearby works plus the classical fidelity references. Semantic Scholar's citation list returned HTTP 429. Absence of an answer in that searched scope does not establish an exhaustive citation census or global priority.

The exact measured optimum, the other parameter values, the commuting-transport criterion and the uniform quantitative family bound remain open here. The escape audit remains unfinished under #19175.
