---
slug: zuppardo-ganardi-miller-bandyopadhyay-paterek-2018-nonselective-negativity-optimum
bibkey: zuppardo2019entanglementgain
doi: 10.1103/PhysRevA.99.042319
url: https://arxiv.org/abs/1806.05465v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.result
---

# The two-qubit non-selective measurement optimum N/2 + 1/4 is global

## Problem

M. Zuppardo, R. Ganardi, M. Miller, S. Bandyopadhyay and T. Paterek, *Entanglement gain in measurements with unknown results* (Phys. Rev. A 99, 042319 (2019); arXiv:1806.05465), study how a non-selective measurement in an orthonormal basis changes entanglement. It maps a pure state |φ⟩ to Σ_j |⟨ψ_j|φ⟩|² |ψ_j⟩⟨ψ_j|.
- **The derived optimum.** For two qubits and the measurement bases (28), they derive the largest final negativity: N^max_f − N_i = 1/4 − N_i/2 (Eq. (33)).
- **The open point.** "Although we were not able to provide a proof that this is indeed the optimal choice among all possible measurement bases, we have conducted numerical check which supports optimality."

The verbatim statements are in [the literature note](../Library/QuantumChannels/zuppardo2019entanglementgain.md).

Issue [#18399](https://github.com/the-omega-institute/trureturing/issues/18399) fixes the reading: for every unit two-qubit ψ and every orthonormal basis, the measured state has negativity at most N(ψψ†)/2 + 1/4, and some basis attains it. This is proved.

## Motivation

An unread measurement can create entanglement. Its optimum quantifies the largest entangling effect of a measurement on a given pure input. The source's optimum was derived only within the family (28).

## Gap

Issue #18399 records the literature check before any Lean:
- arXiv v1, the only version, leaves the optimality open, as does the published version;
- the two citing works listed by Semantic Scholar, arXiv:2201.07969 and the 2024 review DOI 10.33102/mjosht.v10i2.408, cite it only for background and do not address the optimality (both read in full; the readings are in a comment on #18399);
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Let ρ = ψψ† and σ = Σ_j p_j P_j with p_j = ⟨e_j, ρ e_j⟩ for an orthonormal basis (e_j).
1. **The reflection identity.** Tr σ² = Σ p_j² = Tr(σρ), so X = 2σ − ρ satisfies Tr X² = 1.
2. **The Frobenius bound.** Partial transposition permutes entries, so ‖X^Γ‖_F = 1, and in dimension 4, ‖X^Γ‖₁ ≤ 2‖X^Γ‖_F = 2.
3. **The bound.** 2σ^Γ = ρ^Γ + X^Γ and the triangle inequality give ‖σ^Γ‖₁ ≤ (‖ρ^Γ‖₁ + 2)/2, that is N(σ) ≤ N(ρ)/2 + 1/4.
4. **Attainment.** Local unitaries rotate ψ to ψ₀ = a|00⟩ + b|11⟩ with a, b ≥ 0. Let Φ = (|00⟩ + |11⟩)/√2 and c = ⟨ψ₀, Φ⟩ = (a + b)/√2.
   - For c < 1, the basis (ψ₀ + Φ)/√(2 + 2c), (ψ₀ − Φ)/√(2 − 2c), |01⟩, |10⟩ produces σ₀ = (ρ₀ + ΦΦ†)/2 with N(σ₀) = N(ρ₀)/2 + 1/4.
   - For c = 1, ψ₀ = Φ is maximally entangled and any basis containing Φ gives σ₀ = ρ₀, with N(σ₀) = 1/2 = N(ρ₀)/2 + 1/4.
   - The Lean proof uses one real orthogonal change of basis of the span of |00⟩ and |11⟩, with parameters defined for all a, b ≥ 0, so it covers both cases.

## Falsifier

The theorem would not settle the question if the module's measurement differed from the source's post-measurement state, or its negativity from the source's N. The module takes:
- the basis of the columns of a unitary U and the weights from the diagonal of Uᴴ ρ U;
- the negativity (‖ρ^Γ‖₁ − 1)/2, which is 1/2 for a maximally entangled two-qubit state as in the source.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.lean` (412 lines).
- **Definitions.** It defines `measured` and `claim`, and proves `result : claim`.
- **Reuse.** It reuses:
  - the rank-one density of `PureStateHandshake`;
  - the negativity of `NegativityReductionInclusionRefutation`;
  - the trace-norm lemmas of `FiniteTraceDistance`;
  - the trace-norm/Hilbert–Schmidt bound `traceNorm_mul_le_hsSq` of `TavakoliMorelliIncompleteEAM`. This owner is made public at that theorem by removing `private`, and is re-pinned;
  - the partial-transpose covariance `partialTransposeB_kronecker_conj` of `KickedIsingNegativityRefutation`, extracted there from a local fact of its `result` with the same statement and proof, and re-pinned.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations** (all `declared_validated`):
  - `Reg/D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.lean` (`result`);
  - `Reg/D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM.lean` (`traceNorm_mul_le_hsSq`);
  - `Reg/D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation.lean` (`partialTransposeB_kronecker_conj`).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.lean.json`, statement `sha256:8a8a0bbee91a0db7c470231dd2a8e0a8fbf4d1ea632a6352cba3ac9d6adbe5da`.

Declaration statements:
- `result`: `sha256:d15d2b1b270580c6f761f92e449227bdbf9887f85aee1a3b3356367b6acd50e6`;
- `claim`: `sha256:77af19143f9d4dc5211873945a4f43a21b9de71fe2b36a6094f9bcf007cbdbcd`.

## Triage

Tier 1 open question of a 2018 paper (published 2019), preregistered in issue #18399 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the reflection identity, the Frobenius bound, the triangle inequality and the attaining state are instantiations of existing lemmas and finite matrix identities | open-problem-resolution |
| `measured`, `claim` | bind-only | none | definitions used by `claim` |
| the pinching, Frobenius, Schmidt and attainment helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The module is a general theorem over all pure two-qubit states and all measurement bases, so `utility` is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** max over all orthonormal bases of the negativity after the non-selective measurement equals N(ρ)/2 + 1/4 for every pure two-qubit ρ. So the gain is 1/4 − N(ρ)/2, the global optimality of Eq. (33).

**Computed, not formalized** (orchestrator, recorded in #18399): over 200 000 random pure states and Haar-random bases, N(D_B(ρ)) − (N(ρ)/2 + 1/4) stays at most −0.0096.

**Argued, not formalized.**
- *Mechanism.* On pure states, 2D_B − id is a Hilbert–Schmidt reflection: the measured change X has unit Frobenius norm whatever the basis. The bound is the equality case of ‖X^Γ‖₁ ≤ 2‖X^Γ‖_F in dimension 4 together with the triangle inequality, and the half-pure, half-Bell output attains both.
- *Scope.*
  - For a mixed input, Tr(σρ) = Tr σ² still holds, so Tr X² = Tr ρ². The same steps give N(σ) ≤ N(ρ)/2 + (2√(Tr ρ²) − 1)/4. This bound is not formalized, and its attainment is not settled.
  - For d × d systems the factor 2 becomes d, which gives N(σ) ≤ N(ρ)/2 + (d − 1)/4. The source's Theorem 3, Eqs. (15)–(17), measures a non-maximally entangled input φ in a basis containing (φ ± Φ)/√(2 ± 2⟨φ, Φ⟩) and obtains the output (φφ† + ΦΦ†)/2 with negativity N(φ)/2 + (d − 1)/4, so the d × d bound is attained. Neither the d × d bound nor its attainment is formalized.

**Effect on the paper.** The numerically supported optimum of Section I.E holds for every measurement basis. The free-lunch discussion (negativity gain only for non-maximally entangled inputs) follows from the formula.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
