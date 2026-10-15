---
bibkey: ghosal2021qubitchannelsteleportation
authors: Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee
year: 2021
title: "Characterizing qubit channels in the context of quantum teleportation"
doi: 10.1103/PhysRevA.103.052422
url: https://arxiv.org/abs/2102.02054v2
claim: "When Alice sends one half of |Ψa⟩ = √a|00⟩ + √(1−a)|11⟩ (1/2 < a < 1) to Bob through a qubit channel, the final state is useful for universal quantum teleportation (|t11| = |t22| = |t33| > 1/3 in the canonical form) for unital channels only if the concurrence exceeds 1/2; for non-unital channels the authors conjecture a critical concurrence 0 < C_Critical ≤ 0.41 (Conjecture 1) and state that they could not determine its precise value."
strata_touched:
  - D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence
license: citation-only
triage: anchor
---

# Ghosal–Das–Banerjee, qubit channels and universal quantum teleportation

A. Ghosal, D. Das and S. Banerjee, *Characterizing qubit channels in the context of quantum teleportation*, Phys. Rev. A **103**, 052422 (2021), DOI 10.1103/PhysRevA.103.052422; arXiv:2102.02054 [quant-ph] (v2).

## Verified locator

DOI: 10.1103/PhysRevA.103.052422 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2102.02054v2 (the latest of versions v1–v2).
Source: https://arxiv.org/pdf/2102.02054v2 (text read from the PDF):
- §II.B, Eq. (3): the canonical form of a two-qubit state under product unitaries;
- §II.C: usefulness, universality and the criterion for universal quantum teleportation (UQT);
- §V: the initial state |Ψa⟩ and its concurrence; §V.2, the two-Kraus non-unital family of Eq. (50), the threshold 0.41 and Conjecture 1.

## Source statements

§II.B, Eq. (3): every two-qubit state is brought by a product unitary U₁ ⊗ U₂ to ρ_C = ¼[I₄ + r·σ ⊗ I₂ + I₂ ⊗ s·σ + Σ_k λ_k |t_kk| σ_k ⊗ σ_k], with λ_k = −1 for |t_kk| ≠ 0 when det(T_ρ) ≤ 0.

§II.C: "A two-qubit state ρ is useful for QT iff F_ρ > 2/3 … universal for QT iff Δ_ρ = 0 … a two-qubit state ρ is useful for Universal Quantum Teleportation (UQT) (i.e., useful and universal for QT) if and only if |t11| = |t22| = |t33| > 1/3."

§V: "Alice prepares a non-maximally entangled two-qubit pure state given by |Ψa⟩ = √a|00⟩ + √(1−a)|11⟩ with 1/2 < a < 1 and sends half of this state to Bob through a qubit channel Λ. The concurrence of the initial state |Ψa⟩ is given by C(|Ψa⟩) = 2√(a(1−a)) with 0 < C(|Ψa⟩) < 1."

§V.2: "the final shared state is useful for UQT when the concurrence of the initial state is strictly greater than √((2/3)(4+√3)(1 − (4+√3)/6)) ≈ 0.41. … we have not found any non-unital qubit channel for which the final state is useful for UQT when the concurrence of the initial state is less than or equal to 0.41. Hence, we can conjecture the following Conjecture 1. If Alice sends one half of any pure entangled state |Ψa⟩ to Bob through any non-unital channel, then the final shared state will be useful for UQT for a strict subset of the non-unital channels if and only if C_Critical < C(|Ψa⟩) < 1, where 0 < C_Critical ≤ 0.41. We could not determine the precise value of C_Critical; further investigations are needed."

## Reading used by the repository

A qubit channel is a finite Kraus family with Σ K†K = I, and it is non-unital when Σ K K† ≠ I. The final state is (id ⊗ Λ)(|Ψa⟩⟨Ψa|). It is useful for UQT when some product of unitaries U ⊗ V brings it to correlation matrix −tI₃ with t > 1/3, the λ_k = −1 canonical form with |t11| = |t22| = |t33| = t of §II.B–§II.C. C_Critical is the infimum of the concurrences for which some channel makes the final state useful for UQT.
