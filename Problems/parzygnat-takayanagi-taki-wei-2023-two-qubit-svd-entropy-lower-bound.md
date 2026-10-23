---
slug: parzygnat-takayanagi-taki-wei-2023-two-qubit-svd-entropy-lower-bound
bibkey: parzygnat2023svdentropy
doi: 10.1007/JHEP12(2023)123
url: https://arxiv.org/abs/2307.06531v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.result
---

# For two qubits the SVD entanglement entropy is at least the smaller of the two entanglement entropies

## Problem

A. J. Parzygnat, T. Takayanagi, Y. Taki and Z. Wei, *SVD entanglement entropy*, JHEP 12 (2023) 123, arXiv:2307.06531v2, define an entropy for a pair of pure states.
- **The SVD entropy.** For |ψ¹⟩, |ψ²⟩ in H_A ⊗ H_B, the reduced transition matrix is τ_A = Tr_B(|ψ¹⟩⟨ψ²|)/⟨ψ²|ψ¹⟩, the SVD density matrix is ρ^{1|2}_A = √(τ_A†τ_A)/Tr √(τ_A†τ_A), and the SVD entanglement entropy is its von Neumann entropy (§2). It lies between 0 and log d_A.
- **The open question.** "In Figure 8, we provide numerical evidence suggesting that a non-trivial lower bound of min{S(ρ¹_A), S(ρ²_A)} might hold for qubits, fails in general for qudits … Rigorous proofs of these observations for qubits … are still lacking" (§3.3). The authors prove it only when the second state is a local unitary image of the first (Eq. (3.37)), "a restricted version of S(ρ^{1|2}_B) ?≥ min{S(ρ¹_B), S(ρ²_B)} (3.38)".

The verbatim statements are in [the literature note](../Library/Entropy/parzygnat2023svdentropy.md).

Issue [#16821](https://github.com/the-omega-institute/trureturing/issues/16821) fixes the reading: two-qubit pure states as coefficient matrices of Frobenius norm 1, the unnormalized transition Tr_B|ψ⟩⟨φ| (the factor 1/⟨φ|ψ⟩ cancels in the SVD density matrix, so orthogonal pairs with nonzero transition are included), and natural-logarithm entropies. The bound is proved for every such pair.

## Motivation

The SVD entropy measures entanglement of a transition between two states. A lower bound by the ordinary entanglement of the states says that a transition is at least as entangled as the less entangled of its endpoints, which is the qubit behaviour the authors observed and could only prove in the equal-entropy case.

## Gap

Issue #16821 records the literature check before any Lean:
- arXiv v1–v2; v2 states the open question and Eq. (3.38);
- Semantic Scholar lists 26 citing works; the full texts of those with arXiv identifiers, together with Caputa–Purkayastha–Saha–Sułkowski (arXiv:2408.06791) and Caputa–Saha–Sułkowski (arXiv:2512.22997), were scanned; none proves the qubit bound, and Chen–Meyer–Xian (arXiv:2508.09261v2) write that "no concrete bound exists between the SVD entropy of τ and the corresponding entanglement entropies of two states";
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Write ψ = Σ A_{ij}|ij⟩ and φ = Σ B_{ij}|ij⟩ with ‖A‖_F = ‖B‖_F = 1, and F(C) = ‖C‖²_F.
1. **Coefficient matrices.** Tr_B|ψ⟩⟨φ| = AB† =: T, ρ_ψ = AA† and ρ_φ = BB†, so det ρ_ψ = |det A|² and det ρ_φ = |det B|².
2. **An adjugate identity.** B†B + adj B (adj B)† = F(B)·1 gives F(AB†) + F(A adj B) = F(A)F(B) = 1, and 2|det C| ≤ F(C) with det(A adj B) = det A det B gives F(T) + 2|det A||det B| ≤ 1.
3. **The square root.** For D = √(T†T), det D = |det T| = |det A||det B| and (Tr D)² = F(T) + 2|det T| ≤ 1.
4. **The determinant comparison.** Q = D/Tr D has det Q = |det A||det B|/(Tr D)² ≥ |det A||det B| ≥ min(det ρ_ψ, det ρ_φ).
5. **Entropy.** The entropy of a 2 × 2 density matrix is an increasing function of its determinant p(1 − p), so S(Q) ≥ min{S(ρ_ψ), S(ρ_φ)}.

## Falsifier

The proof would not settle the question if the module's states were narrower than all two-qubit pure states, if its matrices differed from the source's reduced transition and SVD density matrix, or if its entropy were not the von Neumann entropy. Coefficient matrices of Frobenius norm 1 are exactly the unit vectors of ℂ² ⊗ ℂ²; the module's transition is Tr_B|ψ⟩⟨φ| through the frozen `partialTraceRight`; the SVD density matrix is (Re Tr √(T†T))⁻¹ √(T†T); and the entropy is the frozen `spectralEntropy`, Σ −λ log λ over eigenvalues.

## Evidence

The canonical source is `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.lean` (255 lines).
- It defines `reducedTransition`, `reducedDensity`, `svdDensity` and `claim`, and proves `result : claim`.
- Among its frozen dependencies are `partialTraceRight`, `partialTraceRight_posSemidef` and `spectralEntropy` of `D5/S3/Quantum/Information/PartialTraceMutualInformation`; `pureCoupling` and `pureCoupling_psd` of `D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings`; `qubit_entropy_det`, `qubit_det_bounds` and `Direct.pure_det` of `D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds`; and `trace_pow_add_two` of `D5/S0/Observation/MatrixTracePowerSum`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- Escape registrations: the two owner theorems `Direct.pure_det` and `qubit_det_bounds` of `FormationBounds`, made public for this settlement, are `declared_validated` in `Reg/D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds.lean`. The registrations of `result` (`Reg/D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.lean`) and of `trace_pow_add_two` (`Reg/D5/S0/Observation/MatrixTracePowerSum.lean`) compile but are `declared_unresolved` (judge diagnostic `IE-C050`), so the §3.9 audit is incomplete for those two theorems; the blocker is recorded in issue [#16937](https://github.com/the-omega-institute/trureturing/issues/16937).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.lean.json`, statement `sha256:ece0763383f46f52c46951d974239476fb91c6fd9efade2e65d61c7f9e334b0d`.

Declaration statements:
- `result`: `sha256:8fa028602f4788934d3f9bb8c233d54369dc2d0f057fc6f4c1c0b1943d62e662`;
- `claim`: `sha256:4fb6456bbfc2b3d7dbfe59da08a06ff9b731df8ad4e95b43f5853208143443ba`.

## Triage

Tier 1 question of a 2023 paper, preregistered in issue #16821 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the coefficient-matrix forms, the adjugate identity, the square-root trace and determinant, the determinant comparison and the qubit entropy monotonicity are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the coefficient, adjugate, square-root, determinant and entropy helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every pair of two-qubit pure states with nonzero reduced transition, S(ρ^{1|2}) ≥ min{S(ρ_ψ), S(ρ_φ)}. This is Eq. (3.38) for qubits without the restriction to equal entropies, and the qubit case of the §3.3 lower bound; the same holds for the other subsystem by exchanging the factors.

**Computed, not formalized** (orchestrator, NumPy/SciPy, 14 October 2026): over 200,000 Haar-random qubit pairs the gap S(Q) − min{S(ρ_ψ), S(ρ_φ)} is at least 4.9 × 10⁻⁴; 300 adversarial minimizations reach −3.9 × 10⁻¹⁶ (equality cases); control: at d = 3 the same code finds 5,230 violations among 200,000 pairs, as the source reports for qudits.

**Argued, not formalized.**
- The mechanism is the determinant: for qubits both entropies are increasing functions of the determinant, and det Q ≥ |det A||det B| ≥ min(|det A|², |det B|²). Normalization by the trace of √(T†T) can only increase det Q, because (Tr √(T†T))² ≤ 1 by the adjugate identity.
- For qudits no single invariant controls the entropy, which is consistent with the violations found at d = 3.

**Open.**
- The asymptotic behaviour for large d_A that the source observes (violations becoming rarer); this settlement does not address it.
- Whether the bound is tight away from the equality cases (product states and maximally entangled pairs).

**Effect on the paper.** The qubit lower bound of §3.3, which the authors supported numerically and proved only for local-unitary pairs, holds for every pair of two-qubit pure states.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
