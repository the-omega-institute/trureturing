---
slug: ghosal-das-banerjee-2021-critical-concurrence-universal-teleportation
bibkey: ghosal2021qubitchannelsteleportation
doi: 10.1103/PhysRevA.103.052422
url: https://arxiv.org/abs/2102.02054v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.result
---

# The exact critical concurrence for universal teleportation through qubit channels

## Problem

A. Ghosal, D. Das and S. Banerjee, *Characterizing qubit channels in the context of quantum teleportation*, Phys. Rev. A 103, 052422 (2021), arXiv:2102.02054v2, send one half of |Ψa⟩ = √a|00⟩ + √(1 − a)|11⟩ (1/2 < a < 1, concurrence C = 2√(a(1 − a))) through a qubit channel Λ and ask when the final state (id ⊗ Λ)(|Ψa⟩⟨Ψa|) is useful for universal quantum teleportation (UQT).
- **The criterion.** A two-qubit state is useful for UQT if and only if, in its canonical form under product unitaries, |t₁₁| = |t₂₂| = |t₃₃| > 1/3 (§II.B–§II.C).
- **Unital and non-unital channels.** Unital channels need C > 1/2. For the two-Kraus non-unital family of Eq. (50), the final state is useful for UQT exactly when C > √((2/3)(4 + √3)(1 − (4 + √3)/6)) ≈ 0.41.
- **The question.** Conjecture 1 states that the final state is useful for UQT for some non-unital channels if and only if C_Critical < C < 1, "where 0 < C_Critical ≤ 0.41. We could not determine the precise value of C_Critical; further investigations are needed."

The verbatim statements are in [the literature note](../Library/QuantumChannels/ghosal2021qubitchannelsteleportation.md).

Issue [#16624](https://github.com/the-omega-institute/trureturing/issues/16624) fixes the reading: "useful for UQT" means that some product of unitaries brings the state to correlation matrix −tI₃ with t > 1/3, and channels are finite Kraus families. The question settled is the precise value of C_Critical: C_Critical = C_* = √(5 − 2√3)/3 = 0.4131045583…, the exact value of the source's radical. The source's printed bound "C_Critical ≤ 0.41" is the rounding of that radical; taken literally as the rational 41/100 it would be false, so the settlement answers the precise-value question and does not assert the printed inequality. Conjecture 1's further clause that only a strict subset of the non-unital channels succeeds is not part of the formal statement.

## Motivation

C_Critical is the least entanglement of the initial pure state for which some qubit channel on Bob's side can still deliver a state that teleports every input state with fidelity above the classical 2/3. Between C_* and 1/2, only non-unital, dissipative channels succeed, which is the paper's observation that dissipation can help teleportation.

## Gap

Issue #16624 records the literature check before any Lean:
- arXiv v1–v2; v2 states Conjecture 1 and that the precise value of C_Critical was not determined;
- Semantic Scholar lists 8 citing works, whose full texts were scanned for the critical concurrence, "0.41", "UQT" and "universal quantum teleportation"; none determines C_Critical;
- Crossref, Zenodo and web searches return no determination;
- the repository had no teleportation module and no entry for the paper.

`not-found-in-searched-scope`.

## Route

Put r = 2a − 1 = √(1 − C²), the length of Alice's Bloch vector, which every channel on Bob and every unitary on Alice preserves.
1. **Two positivity conditions.** Suppose a product unitary brings the final state ρ′ to correlation matrix −tI with t > 1/3. Let n be the unit direction of Alice's Bloch vector, P± = (I ± n·σ)/2 and β = tr(ρ′ I ⊗ n·σ).
   - The corner tr(ρ′ P₋ ⊗ P₋) ≥ 0 gives r + β ≤ 1 − t.
   - Cauchy–Schwarz for X ↦ tr(ρ′X), applied to P₊ ⊗ P₋ and its product with the swap, gives (r − β)² ≤ (1 − t)(1 + 3t).
2. **Elimination.** These give r² + rt + t² ≤ r + t, which with t > 1/3 forces r < (1 + √3)/3, that is C > C_*.
3. **Attainment.** For r < (1 + √3)/3, the amplitude-damping pair K₀ = diag(√(1 − γ), 1), K₁ = √γ|1⟩⟨0| with γ = (1 − t)/(1 + r) and t = (1 − r + √((1 − r)(1 + 3r)))/2 > 1/3 is non-unital, its output has correlation matrix diag(t, −t, t), and conjugation by σ_y on Bob turns it into −tI.

## Falsifier

The settlement would not hold if the module's channels were narrower than the source's qubit channels, if its notion of usefulness for UQT differed from the source's criterion, or if C_* were not the source's radical. The module's channels are arbitrary finite Kraus families with Σ K†K = I, which include every qubit channel; its `UsefulUQT` is the canonical correlation matrix −tI with t > 1/3, which is the source's λ_k = −1 canonical form with equal |t_kk|; and √(5 − 2√3)/3 = √((2/3)(4 + √3)(1 − (4 + √3)/6)).

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.lean` (566 lines).
- It defines `psi`, `initial`, `NonUnital`, `out`, `UsefulUQT`, `Cstar`, `conc` and `claim` (trace preservation is the frozen `SwitchUselessConcatenationRefutation.IsKrausChannel`), and proves `result : claim`: for 1/2 < a < 1, every channel making the final state useful for UQT has C > C_*, and for C > C_* some non-unital channel does.
- Among its frozen dependencies are `pauli`, `blochA`, `blochB` and `corr` of `D5/S3/Quantum/Entanglement/SteeringEllipsoidFullyEntangledFraction`, together with its `trace_conj_kron`; `trace_local_right` of `D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation`; `trace_pauli_kronecker_eq_corr` of `D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH`; `spin` of `D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness`; `matrix_energy` of `D5/S3/Quantum/Information/ActualPureQubitCostInfimum`; and Mathlib's `Matrix.trace_units_conj`, `inner_mul_inner_self_le` and positive-semidefinite trace lemmas.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.lean` reads out a ↦ conc a in the necessity clause of `claim`. Its rejected realization, the constant 0, fails at a = 3/4: the sufficiency clause gives a useful channel, and the rejected necessity clause would then force C_* < 0. It is `declared_validated`. The five owner theorems made public for this settlement (`trace_conjugate_left`, `trace_conjugate_right` and `trace_local_right` of `KickedIsingNegativityRefutation`, `trace_conj_kron` of `SteeringEllipsoidFullyEntangledFraction`, `trace_pauli_kronecker_eq_corr` of `SteeringEllipsoidCHSH`) are registered in their modules' `Reg/` mirrors, each `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.lean.json`, statement `sha256:89d0bed6707b07a28b04ff5145937b897b5e2613dba18c61ef48614d20521b04`.

Declaration statements:
- `result`: `sha256:c7ce1d5c620f616cb4761b3dad6d8897d0429a368f3e9145ad9536c0dd742223`;
- `claim`: `sha256:247d322418240697586612a066f8ffc51a145f1257b6148f2f4b38193c744b9e`.

## Triage

Tier 1 question of a 2021 paper, preregistered in issue #16624 before any Lean.
`theorem`; resolution `proved` (the precise value of C_Critical).

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the corner and Cauchy–Schwarz positivity conditions, the elimination, the radical comparison and the amplitude-damping attainment are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the frame, projector, swap, channel and scalar helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every 1/2 < a < 1, some qubit channel on Bob makes the final state useful for UQT if and only if C > C_* = √(5 − 2√3)/3; when C > C_*, an amplitude-damping (non-unital) channel suffices. Hence C_Critical = C_*. Necessity holds for every channel, unital or not.

**Computed, not formalized** (orchestrator, cvxpy/CLARABEL and NumPy, 14 October 2026):
- for seven values of a, a semidefinite program over every qubit channel (its Choi matrix, trace preservation, output correlation matrix −tI) gives the largest t, which agrees with (1 − r + √((1 − r)(1 + 3r)))/2 to within 2.9 × 10⁻⁹;
- at C = C_* ∓ 10⁻³ the largest t is 0.3324263 < 1/3 and 0.3342408 > 1/3;
- control: the level-1 moment relaxation (the Gram matrix of I, σᵢ ⊗ I and I ⊗ σⱼ only) gives the weaker r ≤ 0.9327 at t = 1/3, against the sharp (1 + √3)/3 = 0.9107, so both positivity conditions of step 1 are needed.

**Argued, not formalized.**
- The mechanism: Alice's marginal is fixed by the initial state, and a large Bloch length r leaves too little room for an isotropic correlation −tI with t > 1/3. Positivity of the corner P₋ ⊗ P₋ and of the 2 × 2 block on P₊ ⊗ P₋ and P₋ ⊗ P₊ give the sharp trade-off r² + rt + t² ≤ r + t, and amplitude damping saturates it.
- The source's family (50) attains the same threshold, so it is optimal among all channels.

**Open.**
- Whether the set of successful non-unital channels is a strict subset of the non-unital channels for every C_* < C < 1, as Conjecture 1 also asserts; this settlement does not address it.
- The analogous thresholds for mixed initial states or higher-dimensional systems.

**Effect on the paper.** The precise value C_Critical = √(5 − 2√3)/3 = 0.4131… is the source's own radical; its printed "C_Critical ≤ 0.41" is that value rounded down, so the printed inequality is not literally correct but the source's threshold is exact and optimal.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
