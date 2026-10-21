---
bibkey: xuimaiguhne2023classicalization
authors: Zhen-Peng Xu, Satoya Imai, and Otfried Gühne
year: 2023
title: Fate of multiparticle entanglement when one particle becomes classical
doi: 10.1103/PhysRevA.107.L040401
url: https://arxiv.org/abs/2206.12834v2
claim: Section V.B asks whether both classicalization entanglement-change gaps can be arbitrarily large while the measured party is a qubit.
strata_touched:
  - D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.107.L040401

Source: https://arxiv.org/abs/2206.12834v2

## Statements

Equation (1), page 2: “Φ_C(ρ_ABC) = Σ_i p_i σ_i ⊗ τ_i, where p_i = tr(ρ_ABC m_i), σ_i = tr_C(ρ_ABC m_i)/p_i and τ_i is the register state related to the outcome i”. “We denote by N_C the set of all possible operations in the form in Eq. (1) on the party C … equivalent to the set of entanglement breaking channels”.

Equation (2), page 2: “Δ_E(ρ_ABC) = min_{Φ_C ∈ N_C} {E[ρ_ABC] − E[Φ_C(ρ_ABC)]}”.

Equation (4), page 3: “N_ABC(ρ_ABC) = N_{AB|C} + N_{BC|A} + N_{AC|B}”, where N_{X|Y} “is the negativity for a bipartition X|Y with eigenvalues λ_i of the partial transposed state ρ^{T_Y} with respect to the subsystem Y”.

Equation (9), page 3: “Δ̃_E(ρ_ABC) = E[ρ_ABC] − E[ρ_AB ⊗ |0⟩⟨0|], with ρ_AB = tr_C(ρ_ABC)”.

Section V.B, page 5: “Inspired by those two examples, an interesting question arises whether there exist entanglement measures E and states ρ_ABC such that both Δ_E(ρ_ABC) and Δ̃_E(ρ_ABC) − Δ_E(ρ_ABC) can be arbitrarily large in the sense that they are not limited by the size of C, even if C is only a qubit. We leave this question for further research.”

## Encoding and boundary

The measure is the fixed tripartite negativity of Equation (4). The bipartite negativity is `(traceNorm (partialTranspose ρ) - 1) / 2`. This is positive negativity; the source's printed sum over negative eigenvalues omits an absolute value, while its examples use positive values. The three summands transpose C, A, and B respectively.

All finite measurements and all finite register dimensions enter the infimum defining Δ. A branch is the unnormalized matrix `tr_C(ρ m_i)` and therefore needs no division by an outcome probability. The flag in Δ̃ is the zero basis state of a qubit. The answer uses local carriers `Fin (2*d)` on A and B and `Fin 2` on C, with a normalized maximally entangled factor tensor a W state. Both gaps grow linearly with d; no dimension-dependent rescaling of the entanglement measure is used.

Exhaustive literature priority is ASSUMED-UNVERIFIED. Logarithmic negativity and other measures are outside the proposition.
