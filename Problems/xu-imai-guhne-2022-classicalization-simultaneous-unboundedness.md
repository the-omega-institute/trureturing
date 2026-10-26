---
slug: xu-imai-guhne-2022-classicalization-simultaneous-unboundedness
bibkey: xuimaiguhne2023classicalization
doi: 10.1103/PhysRevA.107.L040401
url: https://arxiv.org/abs/2206.12834v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.result
---

# Two unbounded classicalization gaps with a qubit

## Problem

Zhen-Peng Xu, Satoya Imai and Otfried Gühne, *Fate of multiparticle entanglement when one particle becomes classical*, arXiv:2206.12834v2, Phys. Rev. A 107, L040401, Section V.B, page 5:

> Inspired by those two examples, an interesting question arises whether there exist entanglement measures E and states ρ_ABC such that both Δ_E(ρ_ABC) and Δ̃_E(ρ_ABC) − Δ_E(ρ_ABC) can be arbitrarily large in the sense that they are not limited by the size of C, even if C is only a qubit. We leave this question for further research.

The answer is **Proved** for the fixed tripartite negativity of Equation (4), with no dimension-dependent rescaling. The source and conventions are in [the Library note](../Library/QuantumContext/xuimaiguhne2023classicalization.md); [#19638](https://github.com/the-omega-institute/trureturing/issues/19638) is the preregistration.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| Equation (4), sum of three bipartite negativities | `tripartiteNegativity` | Partial transposes on C, A and B; positive negativity $(\|\rho^{T_Y}\|_1-1)/2$. |
| Equation (1), $\sum_i p_i\sigma_i\otimes\tau_i$ | `branch`, `classicalize` | Unnormalized branches $p_i\sigma_i=\operatorname{tr}_C(\rho m_i)$, including zero-probability outcomes. |
| Equation (2), minimum entanglement loss | `delta` | Infimum over every finite POVM and every finite register dimension; attainment is proved for the constructed family. |
| Equation (9), discard C and prepare its zero flag | `deltaTilde` | The prepared flag is the zero basis state of a qubit. |
| Both gaps arbitrarily large on the same state | `claim`, `result` | Every real threshold admits one positive semidefinite trace-one state on $\operatorname{Fin}(a)\times\operatorname{Fin}(b)\times\operatorname{Fin}(2)$ exceeding it in both gaps. |

The density and POVM conditions appear literally in the public proposition and the infimum. The proofs use the frozen `IsDensity` and `IsPOVM` predicates with those same defining conditions. The source prints a sum of negative eigenvalues without an absolute value; its examples use the standard positive negativity adopted here.

## Motivation

A single qubit can control two distinct losses: the unavoidable loss when its quantum information is replaced by any measurement-and-prepare register, and the further loss caused by discarding that register. The source's flower-state example has zero unavoidable loss and unbounded further loss; Observation 6 gives unbounded unavoidable loss. The settlement supplies one family with both losses unbounded simultaneously.

## Gap

The literature screen in #19638 covers arXiv v1 and v2, Imai's dissertation Section 12.5.2, and the related works arXiv:2501.04526, 2407.13348 and 2402.06677. The recorded screen finds no settlement in those works. Christandl–Winter, quant-ph/0501090, is not read in full. The bounded search result is `not-found-in-searched-scope`; exhaustive priority is `ASSUMED-UNVERIFIED`.

## Route

Let $|\Phi_d\rangle=d^{-1/2}\sum_{r=0}^{d-1}|rr\rangle$ and $|W\rangle=(|001\rangle+|010\rangle+|100\rangle)/\sqrt3$. Regroup $\rho_d=|\Phi_d\rangle\langle\Phi_d|\otimes|W\rangle\langle W|$ onto $A=A'A_0$, $B=B'B_0$ and C. Thus A and B have dimension $2d$ and C has dimension two.

Rank-one refinement of a qubit POVM writes each refined vector as $v_i=\alpha_i|0\rangle+\beta_i|1\rangle$, with $\sum_i|\alpha_i|^2=\sum_i|\beta_i|^2=1$. Its normalized W branch has coefficient matrix $K_i=\left(\begin{smallmatrix}\overline{\beta_i}&\overline{\alpha_i}\\\overline{\alpha_i}&0\end{smallmatrix}\right)/\sqrt3$, giving partial-transpose trace norm $(4|\alpha_i|^2+|\beta_i|^2)/3$. Summing yields $5/3$. Tensor multiplicativity and the trace-norm triangle inequality bound the two A and B output cuts by $5d/3$ each. The output-register cut is positive under partial transpose and has unit trace, hence contributes zero negativity. Computational-basis measurement with orthogonal qubit flags attains the bound.

The compiled private declarations `Family.family_initial`, `Family.family_all_channel_bound`, `Family.family_attains` and `Family.family_discarded_value` establish respectively

$$E(\rho_d)=d-1+\frac{(2d+1)\sqrt2}{3},\qquad \max_{\Phi_C}E(\Phi_C(\rho_d))=\frac{5d}{3}-1,\qquad E(\rho_{AB}\otimes|0\rangle\langle0|)=\frac{d(2+\sqrt5)}3-1.$$

The private `Family.finite_family_data` identifies the infimum with the attained optimum and proves both gap identities:

$$\Delta_E(\rho_d)=\frac{2d(\sqrt2-1)+\sqrt2}{3},\qquad \widetilde\Delta_E(\rho_d)-\Delta_E(\rho_d)=\frac{d(3-\sqrt5)}3.$$

Both slopes are positive. `unbounded_linear_gaps` chooses d for every real threshold, and `result` proves the public `claim`.

## Falsifier

A restriction to a chosen POVM, a fixed outcome count or a bounded register dimension would not settle the stated infimum. The upper bound quantifies all finite outcome types and register dimensions. A dimension-dependent rescaling of E, growth of C, or different states for the two gaps would not answer the question; E is fixed, C is exactly a qubit, and both inequalities use the same state. The public theorem has no hypotheses.

## Evidence

The canonical mathematical source is [XuImaiGuhneSimultaneousUnboundedness.lean](../D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness.lean). Its sole public theorem is `result : claim`. Its public definitions have complete formulas in the corresponding Blueprint. The admission basis is `open-problem-resolution (#19638; Proved)`; there is no atom.

The four-slot escape audit for `D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.result` is unfinished under [#19716](https://github.com/the-omega-institute/trureturing/issues/19716). The dependent threshold-indexed family needs compiled source-reconstruction, equivalence, variation, sensitivity and observational-dependence evidence. No `declared_validated` registration is claimed.

### Numerical experiment

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ea163f303fe0ca0f5bb1c49ce078a3e7c662cc59/docs/reports/xu-imai-guhne-2022-classicalization-simultaneous-unboundedness). Command: `OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 python3 /Users/auric/trureturing-experiments/docs/reports/xu-imai-guhne-2022-classicalization-simultaneous-unboundedness/check.py`; exit 0, `RESULT PASS`. Script SHA-256: `977d6aef0d5b5991e2237a1cdd3030f0888d5eecbb758fe1a2119e41c324ea7e`.

The tested scope is $d=2,3,4$, tolerance $10^{-9}$, 400 random channels per d with 2–4 effects and register dimension 1–3. These are numerical checks, not a proof of the all-channel bound.

| d | $E(\rho_d)$ | Attained output E | Largest sampled output E | $\Delta_E$ | $\widetilde\Delta_E-\Delta_E$ |
| --- | --- | --- | --- | --- | --- |
| 2 | 3.357022604 | 2.333333333 | 2.095592731 | 1.023689 | 0.509288 |
| 3 | 5.299831646 | 4.000000000 | 3.675282957 | 1.299832 | 0.763932 |
| 4 | 7.242640687 | 5.666666667 | 5.129618788 | 1.575974 | 1.018576 |

## Triage

Tier 1 published question; settlement Proved. The scope is finite-dimensional tripartite negativity.

### What the settlement shows

| Target item | Status and evidence kind | Evidence |
| --- | --- | --- |
| One fixed tripartite negativity measure suffices; no dimension-dependent rescaling | Proved; kernel-checked | `result` uses the single definition `tripartiteNegativity` at every threshold. |
| Both gaps grow linearly with d while C stays exactly a qubit | Proved; kernel-checked | Private `Family.finite_family_data` gives the two identities above for every $d\ge2$, and `unbounded_linear_gaps` establishes simultaneous unboundedness. |
| The optimal record can be a qubit with two orthogonal flags | Proved; kernel-checked | Private `WChannel.computational_povm`, `WChannel.computational_state`, `Family.family_attains` and `Family.finite_family_data` use two computational-basis flags on `Fin 2` and prove attainment. |
| Output-register cut contributes zero negativity; amplification acts through A and B cuts | Proved; paper argument from kernel-checked identities | Private `WChannel.output_normC_eq` gives raw trace norm 3; `Amplification.amplify_normC` multiplies it by d, and multiplication by $(3d)^{-1}$ gives trace norm 1 and negativity $(1-1)/2=0$. `Amplification.amplify_normA` and `Amplification.amplify_normB` give the additional factor d on the other normalized cuts. |
| Experiment readings | Computed; floating-point experiment | The pinned experiment entry tests precisely $d=2,3,4$ and 400 sampled channels per d. |
| Exhaustive literature priority | Open; incomplete literature screen | The scope and unread work are stated in Gap. |
| Logarithmic negativity and other measures | Open | No theorem in this module establishes these extensions. |

The decisive mechanism is the POVM-independent branch-norm sum followed by entanglement amplification in A and B. It supplies the simultaneous example left open by Section V.B; it does not alter the source's flower-state or Bell-pair results. No extension to infinite-dimensional registers or to other entanglement measures is claimed.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are `ASSUMED-UNVERIFIED`. The numerical experiment is approximate and finite. The four-slot escape audit remains unfinished under #19716; it is separate from the kernel proof of the settlement.
