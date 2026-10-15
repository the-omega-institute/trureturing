---
slug: mitra-badhani-ghosh-2023-completely-useless-concatenation
bibkey: mitrabadhanighosh2023switch
doi: 10.1088/1402-4896/acbcf7
url: https://arxiv.org/abs/2108.14001v6
triage: theorem
motivation_gids:
  - D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.result
---

# Two completely useless channels with a useful concatenation switch branch

## Problem

A. Mitra, H. Badhani and S. Ghosh, *Improvement in quantum communication using quantum switch*, Phys. Scr. 98, 045101 (2023), arXiv:2108.14001v6, Section III.B, Conjecture 1:

> Concatenation of two completely useless channels is always completely useless.

The preceding definition is:

> A useless channel is completely useless if under both C+ and C− it remains useless.

Here uselessness concerns entanglement transfer and means entanglement breaking. Equation (8) gives the two completely positive switch branches with Kraus operators $(K_iK_j\pm K_jK_i)/2$. These branches need not preserve trace. The conjecture concerns normalized channels, together with entanglement breaking of their original map and both branches.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Qubit Kraus matrices and completeness | `IsKrausChannel`, complex matrices on `Fin 2`, and the sum of $K_i^\dagger K_i$ equal to the identity | Literal normalization; no extra hypothesis |
| Kraus sum action | Existing `MatrixMap.of_kraus K K` | The sum of $K_iXK_i^\dagger$; no new forwarding definition |
| Equation (8), plus branch | `switchPlus` | Anticommutator Kraus operators divided by two |
| Equation (8), minus branch | `switchMinus` | Commutator Kraus operators divided by two |
| Complete uselessness | `CompletelyUseless` | All three entanglement-breaking conjuncts, using the existing `IsEB` |
| Concatenation, second after first | `composeKraus L K` | The pair $(i,j)$ carries $L_jK_i$ |
| Every pair of such channels | `claim` | Every pair of finite index types, both Kraus families, both normalization hypotheses and both complete-uselessness hypotheses |
| Refutation | `result : ¬ claim` | A single pair satisfying all premises and violating the conclusion suffices |

Finite index types are the Kraus-family convention of [#16400](https://github.com/the-omega-institute/trureturing/issues/16400). `Fintype` arguments are typeclass arguments, with no extra decidability assumption in the claim. The six public definitions state those conventions; the counterexample construction and all proof helpers are private.

## Motivation

The source reports approximately $10^7$ sampled pairs from Pauli and restricted nonunital families. Relative orientation of two dephasing axes matters for concatenation. The qubit counterexample distinguishes the source's universal assertion from the restricted configurations it sampled.

## Gap

This is the Tier-1 published conjecture preregistered in [#16400](https://github.com/the-omega-institute/trureturing/issues/16400). The source and its equation/definition checks are attributed there to the Claude Code orchestrator. The codex-cli literature screen found no answer in six citing full texts (2510.16485, 2506.04607, 2407.02726, 2310.04819, 2206.11032, 2111.08266), two later-author full texts (2405.05326, 2604.01217), or Mitra's thesis Section 6.3.2, printed page 136, which repeats the conjecture.

Three citing full texts were unavailable: DOI 10.1007/s11128-026-05117-0, 10.1145/3647444.3647882 and 10.1109/TWC.2022.3232158. Their direct requests did not yield readable full texts and the Firecrawl requests returned HTTP 402. Absence of an answer in the searched literature does not establish priority or completeness.

## Route

Write $D_u(X)=(X+\sigma_uX\sigma_u)/2$ and $D(X)=\operatorname{Tr}(X)I/2$. Take $A=\eta D_z+(1-\eta)D$ and $B=\eta D_n+(1-\eta)D$, where $\eta=24/25$ and $n=(4/5,0,3/5)$. The four Kraus weights are $7/10,1/10,1/10,7/10$.

The private `channel_A` and `channel_B` check normalization. The six `base_A_prepare`, `base_B_prepare`, `plus_A_prepare`, `plus_B_prepare`, `minus_A_prepare` and `minus_B_prepare` identities give eight-term positive measure-and-prepare representations. The six `eb_*` helpers apply the existing `IptPptSquaredEquivalence.prepare_eb` directly. Its generic statement implies separable output for every PSD amplified input; the proof needs no PPT-to-separability converse.

The private `sep_pt_psd` applies matrix positivity under transpose, Kronecker product and finite sums to the rank-one-product definition of `SEP`. `notEB_of_witness` applies an assumed entanglement-breaking map to the maximally entangled PSD projector, identifies the output with its unnormalized Choi matrix, and contradicts positive semidefiniteness of its partial transpose.

## Falsifier

For $w=(-2,-1,-1,2)$, `witness_value` proves the quadratic value of the output-first partial transpose of the unnormalized Choi matrix of $C_-(B\circ A)$ is $-2185891/39062500<0$. The private `totalG` checks a Gaussian-integer sum of 256 commutator terms equal to $-13989702400$; scaling and coercion yield the rational value. `result` contradicts the minus-branch conjunct of `claim` at this normalized, completely useless pair.

## Evidence

The settling declaration is `D5.S3.QuantumChannels.SwitchUselessConcatenationRefutation.result` in `D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation.lean`, with its canonical Blueprint Scribe and rendered mirror. It has `proof_shape: bind-only` and `admission_basis: open-problem-resolution (#16400; Refuted)`; the settlement uses the external named-conjecture admission rule and claims no new escape witness.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The audit of the newly public owner `IptPptSquaredEquivalence.prepare_eb` is unfinished: [#16693](https://github.com/the-omega-institute/trureturing/issues/16693) identifies the missing faithful dependent-domain reconstruction, enrolled readout and realization/variation/sensitivity evidence. No completed registration is claimed.

### Experiment

The independent numerical check is in [the experiment directory at commit c7aada3ab13fd51b2a9345d44368539005eae5c5](https://github.com/the-omega-institute/trureturing-experiments/tree/c7aada3ab13fd51b2a9345d44368539005eae5c5/docs/reports/mitra-badhani-ghosh-2023-completely-useless-concatenation). Command: `python3 check.py` using that pinned `check.py`; exit 0, `ALL_OK`. SHA-256: `d7c02094b51832f8c54bfbd2ed0d30d3d87dd524380b9c12b119cf7256152c6d`.

The exact Gaussian-rational computation tests only $\eta\in\{19/20,39/40,99/100\}$ at tilt $(4/5,0,3/5)$. At each point all principal minors of the partial transposes of the four factor switch-branch Choi matrices are nonnegative. The normalized Choi witness divided by ten agrees with $(9\eta^4-150\eta^2+125)/2000$ and is negative. The values are respectively $-487111/320000000$, $-24219031/5120000000$ and $-1336963591/200000000000$. These finite readings establish neither a uniform interval nor a two-parameter region.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked instance.** At $\eta=24/25$, `channel_A`, `channel_B`, `useless_A`, `useless_B`, `witness_value` and `result` certify the failure for two nonparallel axes. The minus branch takes commutators of the composed Kraus operators; its negative partial-transpose value certifies entangling output even though each factor's original map and both branches break entanglement. This explains the role of relative orientation; no general classification of commutators is claimed as a Lean theorem.
- **Family — computed finite readings; uniform extension open.** The experiment verifies the displayed witness polynomial and branch PPT checks at exactly the three listed values. The proposed family $19/20\le\eta<1$ is a follow-up candidate, not a kernel-checked family theorem. Conditional on the polynomial being the witness throughout that interval, its negativity follows in prose: setting $x=\eta^2\le1$ gives derivative $18x-150<0$, and the polynomial is already negative at $\eta=19/20$. Uniform identification of the witness and complete uselessness throughout the interval remain open here. The full $(\eta,\mathrm{tilt})$ region is also open in this delivery because the pinned experiment contains no tilt sweep or uniform certificate.
- **What survives — open.** The conjecture restricted to common-axis Pauli channels or the authors' sampled nonunital family is not settled. Neither the Lean instance nor the experiment proves either restriction.
- **Source consequences — proved by the counterexample; other results retain their own hypotheses.** The unrestricted Conjecture 1 is false. A deduction requiring its unrestricted truth loses that premise. Equation (8), the definition of complete uselessness and the source's sampled observations are not contradicted by this instance. No theorem concerning classical capacity, perfect deterministic transmission or physical implementation follows from this entanglement-transfer refutation.

## ASSUMED-UNVERIFIED

Literature priority and completeness beyond the retrieved texts, including the three unavailable citing texts, are `ASSUMED-UNVERIFIED`. The one-parameter interval and the full tilt region are unproved here. The newly public owner theorem has the unfinished audit linked above. No assertion of experimental realization or classical communication capacity is made.
