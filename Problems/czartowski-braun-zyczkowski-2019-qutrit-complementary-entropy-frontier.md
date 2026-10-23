---
slug: czartowski-braun-zyczkowski-2019-qutrit-complementary-entropy-frontier
bibkey: czartowski2019tradeoff
doi: 10.1142/S0219749919500461
url: https://arxiv.org/abs/1908.03492v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.result
---

# The lower boundary of the entropy region of qutrit channels and their complements is the conjectured curve

## Problem

J. Czartowski, D. Braun and K. Życzkowski, *Trade-off relations for operation entropy of complementary quantum channels*, Int. J. Quantum Inf. 17, 1950046 (2019), arXiv:1908.03492v1, study the pairs (S_map(Φ), S_map(Φ̃)) of the map entropy of a channel and of its complementary channel.
- **The map entropy.** S_map(Φ) is the von Neumann entropy of the normalized Choi state. By Proposition 1, S_map(Φ) = S(Φ̃(I/N)) and S_map(Φ̃) = S(Φ(I/N)).
- **The conjecture.** Conjecture 1 (page 5): "For qutrit channels with qutrit environment the lower boundary of the allowed set A_3 is given by the parametric curve p(a) = (−a log a − (1 − a) log(1 − a), log 3/3 − (a + 1/3) log(a + 1/3) − (a − 1/3) log(a − 1/3)) (20) with a ∈ (0, 1/3), together with reflection through line S = S̃".

The verbatim statements are in [the literature note](../Library/QuantumChannels/czartowski2019tradeoff.md).

Issue [#17038](https://github.com/the-omega-institute/trureturing/issues/17038) fixes the reading:
- The last term of Eq. (20) is read as −(1/3 − a) log(1/3 − a): the printed term is not real for a < 1/3, and the source's attaining channels give the corrected one.
- Put h(a) = H(1 − a, a) and g(a) = H(1/3 + a, 1/3, 1/3 − a). The lower boundary means two things for a ∈ [0, 1/3]:
  - for every isometry V : ℂ³ → ℂ³ ⊗ ℂ³, S_map(Φ) ≤ h(a) implies S_map(Φ̃) ≥ g(a), and the same with Φ and Φ̃ exchanged;
  - the curve and its reflection are attained.

The conjecture is proved in this reading.

## Motivation

The trade-off between the map entropies quantifies how the information leaking to the environment constrains the information kept by the system (§III). For qubit channels the source describes the lower boundary exactly; for qutrits it was known only numerically (Figure 2).

## Gap

Issue #17038 records the literature check before any Lean:
- arXiv v1 is the only version;
- the citing works Duarte–Catani–Drumond (arXiv:2102.11168) and Czartowski–Müller–Życzkowski–Braun (arXiv:2103.02031), read in full, do not treat the qutrit boundary;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Let P = VV†/3, a state on B ⊗ E with marginals ρ_B and ρ_E.
1. **The bridge.** The normalized Choi state of Φ has the same entropy as ρ_E, so S_map(Φ) = S(ρ_E) and S_map(Φ̃) = S(ρ_B), which is Proposition 1 for this setting. The proof compares the characteristic polynomials of the Choi matrix and of the reshuffled Gram matrix.
2. **The spectral table.** Conjugating P by U ⊗ Z, with U and Z the eigenbases of ρ_B and ρ_E, does not change the marginal spectra (local-unitary covariance of the partial traces). The diagonal of the conjugated state is a 3 × 3 table w of entries in [0, 1/3], since 3P is a projection. The entries sum to 1, the row sums are the spectrum of ρ_B, and the column sums are the spectrum of ρ_E.
3. **The table trade-off.**
   - If the row entropy is at most h(a), some row sum is 1 − u with u ≤ a.
   - Every column sum then lies in [1/3 − u, 1/3 + u]: the entries of that row are at least 1/3 − u, and the other rows total u.
   - A distribution in that box with sum 1 has entropy at least g(u), by two-point spreading of −x log x.
   - g(u) ≥ g(a), since g is decreasing.
4. **Attainment.** The source's channels with Kraus pair diag(1, √(1 − 3a), 1) and √(3a)|1⟩⟨2| reach (h(a), g(a)), and their complements the reflected point.

## Falsifier

The proof would not settle the conjecture if:
- the module's channels were narrower than all qutrit channels with a qutrit environment;
- its map entropy differed from the entropy of the normalized Choi state;
- the boundary curve differed from Eq. (20) beyond the misprint;
- the attainment were missing.

The module quantifies over every isometry V : ℂ³ → ℂ³ ⊗ ℂ³, defines the map entropy from the normalized Choi matrix, and states the trade-off in both directions together with exact attainment.

## Evidence

The canonical source is `D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.lean` (586 lines).
- It defines `admissible`, `swap`, `channelB`, `joint`, `rhoB`, `rhoE`, `choi`, `outputEntropy`, `mapEntropy`, `entropy3`, `h`, `g`, `attainer` and `claim`, and proves `result : claim`.
- It uses the frozen `PartialTraceMutualInformation` partial traces and spectral entropy, and the frozen `CapacityMonotone.deterministic_forgetting_entropy_capacity_monotone`. The normalized Choi matrix is one third of `MatrixMap.choi_matrix` of the bundled Kraus map `MatrixMap.of_kraus`, with the pair indices exchanged. `of_kraus` is in the frozen `FiniteKrausChannel`, and `choi_matrix` in the unfrozen `FiniteKrausRepresentation`. It also uses two theorems made public for this settlement:
  - `TruncatedLossDephasingOptimizerRefutation.pair_entropy_le`, the two-point spreading inequality;
  - `KickedIsingNegativityRefutation.trace_local_left`, with the frozen `trace_local_right`, for the covariance.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations, each `declared_validated`:
  - `Reg/D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.lean` reads out the bound g a of the first trade-off direction of `claim`. Its rejected realization, g a + 1, fails at a = 0 and V = `attainer 0`, where `result` gives the complementary entropy g 0 exactly.
  - `pair_entropy_le` is registered in `Reg/D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.lean`.
  - `trace_local_left` is registered in `Reg/D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/QutritComplementaryEntropyFrontier.lean.json`, statement `sha256:1051cd75aae340f720779b961870fa3ee99f5e3e3f94a963c028814f15f02578`.

Declaration statements:
- `result`: `sha256:ca976f7232fadf48c13e3a616377556e805cc911f4377abd022f735f7e08cbdd`;
- `claim`: `sha256:ee5c6b6f6335105175cb49081bc2a40a4d495f59d4b3a9db3f9c1cccca60ad4f`.

## Triage

Tier 1 conjecture of a 2019 paper, preregistered in issue #17038 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the bridge, the spectral table, the table trade-off and the attainment are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the Gram, Choi, spectral, table, entropy and attainment helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 31 private theorems are bind-only helpers consumed on the proof path of `result`, and its 1 private definitions and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every qutrit channel with a qutrit environment and every a ∈ [0, 1/3], S_map(Φ) ≤ h(a) implies S_map(Φ̃) ≥ g(a), and symmetrically. The curve (h(a), g(a)) and its reflection are attained. So the lower boundary of A_3 is the curve of Conjecture 1, read with the corrected Eq. (20), on the closed interval.

**Computed, not formalized** (orchestrator, NumPy, 15 October 2026): over 40,000 random isometries, half of them sparse, the minimum gap to the boundary was 2.5 × 10⁻¹², so no sampled point lay below it. The attaining channels reproduce (g(a), h(a)) to 10⁻⁶ at a ∈ {0, 0.05, 0.1, 0.2, 0.3, 1/3}.

**Argued, not formalized.**
- The mechanism is the spectral table. The joint state is a scaled projection, so the table of its diagonal in the product eigenbasis has entries at most 1/3. A dominant row eigenvalue 1 − u then confines every column sum to [1/3 − u, 1/3 + u], which is exactly the majorization by (1/3 + u, 1/3, 1/3 − u) that the boundary needs.
- The marginal constraints used here are a special case of Higuchi's criterion for one-particle reduced states of three qutrits (quant-ph/0309186, Theorem 1), applied to a purification of P (preregistration #17038; search seat).

**Open.**
- The lower boundary for qudit channels, N ≥ 4, and for qutrit channels with other environment dimensions, which this settlement does not determine.

**Effect on the paper.** Conjecture 1 holds with the corrected Eq. (20): the lower boundary of the entropy region of qutrit channels and their complements is the conjectured curve and its reflection.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The journal version was not read; its agreement with arXiv v1 is unverified. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
