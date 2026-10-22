---
slug: li-theil-harrow-chuang-2026-purify-and-clone-optimality
bibkey: litheilharrowchuang2026coherent
doi: 10.48550/arXiv.2605.21457
url: https://arxiv.org/abs/2605.21457v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.result
---

# Purify-and-clone fails one-site worst-case optimality

## Problem

Z. Li, E. Theil, A. W. Harrow and I. Chuang, *An Exponential Sample-Complexity Advantage for Coherent Quantum Inference*, [arXiv:2605.21457v2](https://arxiv.org/abs/2605.21457v2), Section S3 A, p. 9, states:

> This channel is optimal for m ≤ n (see Ref. [S2]), and we conjecture that it is also optimal for m > n.

[Preregistration #19410](https://github.com/the-omega-institute/trureturing/issues/19410) fixes $n=1$, $m=2$ and the one-site worst-case squared-infidelity reading. The universal optimality assertion is refuted by $d=r=2$. A strict-improvement theorem for every $d\ge r\ge2$ is not part of this settlement. The [Library note](../Library/QuantumContext/litheilharrowchuang2026coherent.md) identifies the source and conventions.

### Statement echo

| Source clause or binding convention | Lean counterpart |
| --- | --- |
| Squared fidelity and infidelity | `sqFidelity` is the squared real trace of the positive square root; the loss uses one minus that value. |
| All purifications, equation (S34) | `purifications` contains every positive trace-one rank-one matrix with the specified environment partial trace. |
| One joint system-environment site | `oneSiteMarginal` retains both registers of either output pair. |
| One common target before the maximum, equation (S13) | `oneSiteLoss` takes the infimum over the convex hull of purifications after forming the maximum of the two infidelities. |
| Worst-case rank-at-most-$r$ domain, equation (7) | `worstCaseOneSiteRisk` takes the supremum over every canonical density state with matrix rank at most $r$. Infima and suprema use `EReal`. |
| Totally symmetric output restriction | `TotallySymmetricSupport` asserts $S\Xi S=\Xi$, with $S=(I+F)/2$, on both sides. |
| Werner cloner and the one-input RP map | `wernerOneToTwo`, `randomPurifyOne` and `purifyAndClone` retain the source matrix expressions, with cloning dimension $dr$. |
| Genuine channel competitors | `AdmissibleChannel` uses `QuantumChannel` and the support restriction on every admissible input. |
| Positive dimensions $1\le r\le d$ | `claim` retains these quantifiers; the counterexample instantiates them at two. |
| Claimed optimality | `claim` compares the two worst-case risks for every admissible channel; `result` proves its negation. |

## Motivation

The settling GID is `D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.result`. Cloning the entire system-environment register and cloning the system before adjoining a symmetric environment have different one-site risks. The latter supplies a strictly better admissible channel in dimension two.

## Gap

The source and literature screen recorded in #19410 includes source versions 1 and 2, Werner's cloning literature and fidelity monotonicity. No settlement was located in that searched scope. Literature completeness is `ASSUMED-UNVERIFIED`. The source's unqualified word “optimal” admits different losses; this dossier settles precisely the one-site worst-case reading.

## Route

For $d=r=2$, apply the system Werner cloner, tensor with one third of the symmetric projector on the two environment registers, and reorder the four registers into two joint sites. The consumed private theorems `competitor_channel` and `competitor_support` certify complete positivity, trace preservation and both-sided symmetric support. Both marginals equal the same system depolarization tensored with $I_2/2$.

A four-element Pauli average puts $\rho\otimes I_2/2$ in the common target convex hull. `competitor_risk_upper` bounds its worst-case risk by $1/6$. At the pure zero input, `purifyAndClone_risk_lower` bounds the purify-and-clone worst-case risk below by $1/5$. `result` combines these inequalities to refute the universal assertion.

## Falsifier

The comparison requires the complete rank-at-most-two input domain, both registers at each site, a common target chosen before the maximum, squared fidelity, genuine CPTP competitors and both-sided total symmetric support. A theorem for another loss, a sampled input set or swap conjugation alone would not settle this statement.

## Evidence

[Canonical Lean source](../D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.lean) and its [Blueprint mirror](../Blueprint/D5/S3/Quantum/Information/LiTheilHarrowChuangPurifyCloneRefutation.md). Admission basis: `open-problem-resolution (#19410; Refuted)`. The new module's declaration classifications are `bind-only`; its private helpers have named consumers, and the settling theorem is admitted as the externally preregistered named-problem resolution. No escape witness is claimed.

The module has `utility: none`. Its public `result` therefore has no designated-refutation registration exemption. Its escape audit, including the generated `sqFidelity.congr_simp` theorem, and that of the published owner helpers `BroadcastingChannelExtremaRefutation.density_le_one`, `WassersteinComplexityNonconvex.trace_sqrt_sq_le_two` and `WassersteinComplexityNonconvex.pure_diag_coupling` are unfinished under [#19490](https://github.com/the-omega-institute/trureturing/issues/19490). No validated registration is asserted.

Experiment: [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ba1a4b17dbf1d2761f12e12eadf076d4facb0e8b/docs/reports/li-theil-harrow-chuang-2026-purify-and-clone-one-site). Command: `python3 check.py` in that directory; exit 0, `RESULT PASS`; script SHA-256 `3d272d84388b46f3f85274842c8eea91c119b107774a6fd2f066f22d23511cbd`. The deterministic experiment tests exactly $(d,r)\in\{(2,2),(3,2),(3,3),(4,2)\}$, with 60 sampled states for each pair. It checks marginal formulas, symmetric support and sampled worst-case risks against the displayed formulas with tolerance $10^{-7}$. The sampled risk pairs are $(0.2000000000,0.1666666667)$, $(0.2857142857,0.2500000000)$, $(0.3000000000,0.2500000000)$ and $(0.3333333333,0.2999999955)$. This is a finite numerical reading; it proves neither a uniform family nor an exact optimum.

### Declaration classification and consumption

All source declarations are classified `bind-only` after expansion of same-delivery helpers. This is a proof-shape classification; the named external problem supplies the admission basis. Private identifiers below are source-qualified names; compiler-generated congruence support is identified separately. Consumers come from the elaborated declaration values. The independent consumption checks establish the live use of each source helper.

| Declaration | Kind | proof_shape | Consumers |
| --- | --- | --- | --- |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqFidelity` | def | bind-only | `oneSiteLoss`, `congr_simp`, `competitor_fidelity_lower`, `competitor_loss_upper`, `oneSiteLoss_ge_of_fidelity`, `oneSiteLoss_le_of_fidelity`, `pure_target_fidelity_bound`, `purifyAndClone_loss_lower`, `sqFidelity_ge_of_order`, `sqFidelity_tensor_same_density` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.purifications` | def | bind-only | `oneSiteLoss`, `oneSiteLoss_ge_of_fidelity`, `oneSiteLoss_le_of_fidelity`, `purifyAndClone_loss_lower`, `randomPurify_mem_target`, `target_density_and_marginal` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.oneSiteMarginal` | def | bind-only | `oneSiteLoss`, `eq_1`, `competitor_loss_upper`, `oneSiteLoss_ge_of_fidelity`, `oneSiteLoss_le_of_fidelity`, `purifyAndClone_loss_lower`, `purifyAndClone_pure_marginal` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.oneSiteLoss` | def | bind-only | `worstCaseOneSiteRisk`, `loss_le_worstCase`, `oneSiteLoss_le_of_fidelity`, `purifyAndClone_risk_lower`, `worstCase_le_of_loss` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.worstCaseOneSiteRisk` | def | bind-only | `claim`, `result`, `purifyAndClone_risk_lower`, `refute_of_risk_bounds` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.TotallySymmetricSupport` | def | bind-only | `AdmissibleChannel`, `competitor_admissible`, `competitor_support` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.wernerOneToTwo` | def | bind-only | `purifyAndClone`, `eq_1`, `competitor`, `competitor_marginal_left`, `competitor_marginal_right`, `competitor_support`, `kraus_action`, `werner_swap_left`, `werner_swap_right` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.randomPurifyOne` | def | bind-only | `purifyAndClone`, `eq_1`, `competitor_fidelity_lower`, `competitor_loss_upper`, `competitor_marginal_left`, `competitor_marginal_right`, `pauli_average`, `pure_target_fidelity_bound`, `purifyAndClone_loss_lower`, `purifyAndClone_pure_marginal`, `randomPurify_mem_target` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.purifyAndClone` | def | bind-only | `claim`, `eq_1`, `purifyAndClone_loss_lower`, `purifyAndClone_pure_marginal`, `purifyAndClone_risk_lower`, `refute_of_risk_bounds` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.AdmissibleChannel` | def | bind-only | `claim`, `result`, `competitor_admissible`, `refute_of_risk_bounds` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.claim` | def | bind-only | `result`, `refute_of_risk_bounds` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.trace_re_mono` | theorem | bind-only | `sqFidelity_ge_of_order` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqrt_sandwich_self` | theorem | bind-only | `sqFidelity_ge_of_order`, `sqFidelity_tensor_same_density` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqFidelity_ge_of_order` | theorem | bind-only | `competitor_fidelity_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.symmetricProjector_apply` | theorem | bind-only | `symmetricProjector_swap_left`, `symmetricProjector_swap_right` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor` | def | bind-only | `result`, `eq_1`, `competitor_admissible`, `competitor_channel`, `competitor_loss_upper`, `competitor_marginal_left`, `competitor_marginal_right`, `competitor_risk_upper`, `competitor_support`, `kraus_action` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.kraus` | def | bind-only | `competitor_channel`, `eq_1`, `kraus_action`, `kraus_complete` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqrtTwo_sq` | theorem | bind-only | `kraus_action`, `kraus_complete` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.kraus_complete` | theorem | bind-only | `competitor_channel` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.kraus_action` | theorem | bind-only | `competitor_channel` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_channel` | theorem | bind-only | `competitor_admissible` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.symmetricProjector_swap_left` | theorem | bind-only | `competitor_marginal_left`, `competitor_support`, `werner_swap_left` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.symmetricProjector_swap_right` | theorem | bind-only | `competitor_marginal_left`, `competitor_support`, `werner_swap_right` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.werner_swap_left` | theorem | bind-only | `competitor_marginal_left`, `competitor_support` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.werner_swap_right` | theorem | bind-only | `competitor_marginal_left`, `competitor_support` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pairSwap_mul_apply` | theorem | bind-only | `competitor_support` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.mul_pairSwap_apply` | theorem | bind-only | `competitor_support` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_support` | theorem | bind-only | `competitor_admissible` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_admissible` | theorem | bind-only | `result` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_marginal_right` | theorem | bind-only | `competitor_loss_upper`, `competitor_marginal_left` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_marginal_left` | theorem | bind-only | `competitor_loss_upper` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.mem_densityMatrices_iff` | theorem | bind-only | `convex_densityMatrices`, `pauli_purifications`, `target_density_and_marginal` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.convex_densityMatrices` | theorem | bind-only | `target_density_and_marginal` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.convex_fixed_marginal` | theorem | bind-only | `target_density_and_marginal` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.target_density_and_marginal` | theorem | bind-only | `purifyAndClone_loss_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.rank_pos_of_trace_one` | theorem | bind-only | `vecPure_rank_one` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.vecPure_rank_one` | theorem | bind-only | `pauli_purifications` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pauliKet` | def | bind-only | `eq_1`, `pauliKet_apply`, `pauli_average`, `pauli_marginal`, `pauli_purifications`, `randomPurify_mem_target` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pauliKet_apply` | theorem | bind-only | `pauli_average` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pauli_marginal` | theorem | bind-only | `pauli_purifications` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pauli_purifications` | theorem | bind-only | `randomPurify_mem_target` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pauli_average` | theorem | bind-only | `randomPurify_mem_target` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.randomPurify_mem_target` | theorem | bind-only | `competitor_loss_upper` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqrt_kronecker` | theorem | bind-only | `pure_target_fidelity_bound`, `sqFidelity_tensor_same_density` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqFidelity_tensor_same_density` | theorem | bind-only | `competitor_fidelity_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqrt_real_smul` | theorem | bind-only | `pure_target_fidelity_bound` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.oneSiteLoss_le_of_fidelity` | theorem | bind-only | `competitor_loss_upper` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.oneSiteLoss_ge_of_fidelity` | theorem | bind-only | `purifyAndClone_loss_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.worstCase_le_of_loss` | theorem | bind-only | `competitor_risk_upper` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.loss_le_worstCase` | theorem | bind-only | `purifyAndClone_risk_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.refute_of_risk_bounds` | theorem | bind-only | `result` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pureZero` | def | bind-only | `eq_1`, `pureZeroDensity`, `_proof_1`, `pureZero_sq`, `pureZero_trace`, `pure_marginal_representation`, `pure_target_fidelity_bound`, `purifyAndClone_loss_lower`, `purifyAndClone_pure_marginal` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pureZero_pos` | theorem | bind-only | `_proof_1`, `pure_target_fidelity_bound` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pureZero_trace` | theorem | bind-only | `_proof_1`, `pure_target_fidelity_bound` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pureZero_sq` | theorem | bind-only | `pure_target_fidelity_bound` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pureZeroDensity` | def | bind-only | `purifyAndClone_loss_lower`, `purifyAndClone_risk_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pure_marginal_representation` | theorem | bind-only | `pure_target_fidelity_bound` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.pure_target_fidelity_bound` | theorem | bind-only | `purifyAndClone_loss_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.purifyAndClone_pure_marginal` | theorem | bind-only | `purifyAndClone_loss_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.purifyAndClone_loss_lower` | theorem | bind-only | `purifyAndClone_risk_lower` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.purifyAndClone_risk_lower` | theorem | bind-only | `result` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_fidelity_lower` | theorem | bind-only | `competitor_loss_upper` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_loss_upper` | theorem | bind-only | `competitor_risk_upper` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.competitor_risk_upper` | theorem | bind-only | `result` |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.result` | theorem | bind-only | terminal settling theorem |
| `D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation.sqFidelity.congr_simp` | theorem (generated) | bind-only | generated simplifier support for `sqFidelity` |


## Triage

Tier 1 externally published conjecture; resolution **Refuted** for the universal one-site worst-case reading by the instance $n=1$, $m=2$, $d=r=2$.

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Dimension-two one-site worst-case refutation | **Kernel-checked:** `result` proves the negation of `claim`, using the strict separation between the bounds $1/5$ and $1/6$. |
| Both AE registers, common convex-hull target, entire rank-at-most-two domain and both-sided symmetric support | **Kernel-checked:** the definitions `oneSiteMarginal`, `oneSiteLoss`, `worstCaseOneSiteRisk` and `AdmissibleChannel` are retained by `result`; `competitor_admissible` supplies support for every density input. |
| Failure mechanism | **Proved in prose:** the supplied system-cloner construction has one-site risk at most $1/6$, whereas the whole-register purify-and-clone map has risk at least $1/5$, by the named Lean bounds. Thus spending the cloning dimension on the environment is unnecessary for this objective. |
| Nearest surviving bound | **Proved in prose:** strict improvement does not contradict the source's upper bound in Theorem S3.1; an upper bound need not equal the optimal risk. The source's $m\le n$ claim is not refuted by an $m>n$ counterexample. |
| Finite numerical family | **Computed:** the pinned experiment entry checks exactly the four dimension pairs and the 60 samples per pair stated there. |
| Optimal RP channel for $m>n$ | **Open:** a better competitor is certified, with no proof of its global optimality. |
| All-site risk | **Open:** equation (S12) is not the loss in `claim`. |
| Average risk | **Open:** equation (8) is not the supremum used by `claim`. |
| General $d\ge r\ge2$ strict-improvement family | **Open:** the Lean refutation uses only $d=r=2$; four sampled dimension pairs do not prove the uniform extension. |
| Other $m>n$ | **Open:** the construction is certified only for $n=1$, $m=2$. |
| Consequences for source results | **Literature reading:** the failed unqualified conjecture supplies no universal optimality certificate for this loss; the source's upper bound and its results for other regimes remain outside the refutation. |
| Literature status | **Literature reading:** no settlement located within the screen in #19410; completeness `ASSUMED-UNVERIFIED`. |

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are unverified. The optimal competitor, all-site and average risks, other copy numbers and the arbitrary-dimension strict-improvement family remain open here. Numerical sampled maxima are not exact worst-case proofs. The four-slot escape audit remains unfinished under #19490.
