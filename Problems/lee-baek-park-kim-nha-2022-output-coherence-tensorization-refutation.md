---
slug: lee-baek-park-kim-nha-2022-output-coherence-tensorization-refutation
bibkey: leebaekparkkimnha2022tensorizedresources
doi: 10.1103/PhysRevResearch.4.043070
url: https://arxiv.org/abs/2104.12307v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.result
---

# The output maximal coherence of channels is not tensorization-stable

## Problem

J. Lee, K. Baek, J. Park, J. Kim and H. Nha, *Fundamental limits on concentrating and preserving tensorized quantum resources*, Phys. Rev. Research 4, 043070 (2022), arXiv:2104.12307, ask whether correlated inputs preserve more of a resource through parallel noisy channels than product inputs.
- For coherence they use the maximal coherence η(ρ) = max_{i≠j} |ρ_ij|/√(ρ_ii ρ_jj) of Lami, Regula and Adesso (Eq. (15)). It governs the fidelity of asymptotic coherence distillation under strictly incoherent operations.
- They define the output maximal coherence η̃(Φ) = max_ρ η(Φ(ρ)) (Eq. (28)).
- **Conjecture 1** (Eq. (29)): η̃(Φ₁ ⊗ Φ₂) = max{η̃(Φ₁), η̃(Φ₂)}. The authors support it with numerics on random channels in dimensions (2, 2) and (2, 3).

The verbatim statements are in [the literature note](../Library/QuantumChannels/leebaekparkkimnha2022tensorizedresources.md).

Issue [#18019](https://github.com/the-omega-institute/trureturing/issues/18019) fixes the reading: for all finite-dimensional channels, given by Kraus families, Eq. (29) holds, with the supremum over all density matrices. This conjecture is refuted.

## Motivation

Conjecture 1 would imply that correlated, in particular entangled, inputs never preserve more maximal coherence through parallel channels than the best single channel. The authors' Conjecture 2 on coherence distillation through joint channels rests on it.

## Gap

Issue #18019 records the literature check before any Lean:
- arXiv v1 and v2 and the journal version keep the conjecture;
- the full texts of two of the three citing works (arXiv:2407.06417 and 2303.07155) do not treat it;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

1. **Witness.** The qubit Pauli channel Φ(ρ) = Σ_σ p_σ σρσ with (p_I, p_X, p_Y, p_Z) = (31/40, 1/10, 1/10, 1/40).
2. **One channel.** Φ([[a, z], [z̄, 1 − a]]) = [[1/5 + 3a/5, 3z/4], [3z̄/4, 4/5 − 3a/5]].
   - The output diagonal product is 4/25 + (9/25)a(1 − a), which is at least a(1 − a) ≥ |z|² because a(1 − a) ≤ 1/4.
   - Hence η(Φ(ρ)) ≤ 3/4 for every input, so η̃(Φ) ≤ 3/4.
3. **Two channels.** For the Bell state, (Φ ⊗ Φ)(ω) has corner entries 9/32 and diagonal entries 17/50 at the corners, so its maximal coherence is 225/272.
4. **Conclusion.** η̃(Φ ⊗ Φ) ≥ 225/272 > 3/4 ≥ max{η̃(Φ), η̃(Φ)}.

## Falsifier

The refutation would not settle the conjecture if:
- the module's η differed from Eq. (15);
- its η̃ restricted the inputs;
- its tensor product of channels differed from Φ₁ ⊗ Φ₂.

The module takes:
- η in the computational basis over pairs with positive diagonal product, with value 0 when there is none;
- η̃ as the supremum over all density matrices, including entangled inputs of the product channel;
- the product channel through the Kraus operators K ⊗ L, which act as Φ₁ ⊗ Φ₂.

## Evidence

The canonical source is `D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.lean` (266 lines).
- It defines `maxCoherence`, the Kraus channel action and normalization, `outputMaxCoherence`, `krausTensor` and `claim`, and proves `result : ¬ claim`.
- It reuses:
  - `DensityState` of `FiniteStateChannel` and the Kraus map `MatrixMap.of_kraus` of `FiniteKrausChannel`;
  - the Bell density of `CHSHWitness`, the Pauli matrices of `PauliThreeWeightBayesianInverseUniqueness`, and the principal-minor bound `psd_entry_bound` of `CartesianVariance`;
  - `CHSHWitness.complex_sqrt_two_inv_mul_self` and `PauliThreeWeightBayesianInverseUniqueness.sigma_properties`, made public by removing only `private`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The newly public `CHSHWitness.complex_sqrt_two_inv_mul_self` and `PauliThreeWeightBayesianInverseUniqueness.sigma_properties` are registered in `Reg/D5/S3/QuantumBounds/CHSHWitness.lean` and `Reg/D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.lean`, both `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/QuantumChannels/OutputMaximalCoherenceTensorizationRefutation.lean.json`, statement `sha256:8127df530cacdb1ce3e7ceafa897974f63d9cebf63e434fece6a157160380bf3`.

Declaration statements:
- `result`: `sha256:65d55f6996294e7080bede26132bc7bc13602d0ff5a7367a96b9cead8354bbca`;
- `claim`: `sha256:e92c35374176c918eaa139b814a505ea6d458c4cd41ffbdd2e614651529a83ca`.

## Triage

Tier 1 conjecture of a 2022 paper, preregistered in issue #18019 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the single-channel bound is a 2 × 2 inequality and the Bell output is a finite rational computation | open-problem-resolution |
| the witness, bound and Bell helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** for the Pauli channel above, η̃(Φ ⊗ Φ) ≥ 225/272 > 3/4 ≥ η̃(Φ). An entangled input preserves strictly more maximal coherence through two parallel copies than any input through one.

**Computed, not formalized** (orchestrator, recorded in #18019):
- η̃(Φ) = 3/4 exactly, with equality at |+⟩⟨+|;
- random two-qubit inputs reach at most 0.714 for Φ ⊗ Φ, below the Bell value; this concerns input sampling for this one channel, while the source sampled random channel pairs and optimized their inputs, so it does not by itself explain the source's numerics.

**Argued, not formalized** (search seat; only the rational member is rechecked). For 1/2 < t < 1 and 2t − 1 < c < √(2t − 1), the Pauli channel with off-diagonal factor t and diagonal contraction c has η̃ = t, while the Bell input gives 2t²/(1 + c²) > t.
- *Mechanism.* In the Bell output, the corner coherence is t²/2 while the corner populations are (1 + c²)/4. A single qubit's output coherence is normalized by the square root of a diagonal product equal to 1/4 at the optimum. The Bell output normalizes the squared coherence factor t² by populations that the diagonal contraction c moves only to second order, so the ratio 2t²/(1 + c²) exceeds t exactly when c² < 2t − 1.

**Open.**
- The exact value of η̃(Φ ⊗ Φ) for this channel, and whether η̃(Φ^{⊗n}) tends to 1.
- Whether Conjecture 2 of the source, on SIO distillation through joint channels, fails as well.

**Effect on the paper.** Correlated inputs can preserve more maximal coherence than product inputs. The no-go statement of §IV.B holds for nonclassicality depth (Theorem 5) but not for maximal coherence.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized", "Argued, not formalized" and "Open" are not formalized.
