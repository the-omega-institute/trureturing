---
bibkey: badhani2026conditionalchannel
authors: H. Badhani and S. Das
year: 2026
title: Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing
doi: 10.48550/arXiv.2604.01217
url: https://arxiv.org/abs/2604.01217v2
claim: "Section VI.1 conjectures that Proposition 10 extends to all unitaries with added white noise, with qubit conditioning."
strata_touched:
  - D5/S3/Quantum/Information/BadhaniDasNoisyUnitary
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2604.01217

Source: https://arxiv.org/abs/2604.01217v2

# Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing

The source is version 2, 23 June 2026. Page numbers refer to the PDF of that version.

Section VI.1, page 31:

> For an arbitrary unitary channel U_{A′B′→AB} such that |B′| = |B| = 2, we have S_∞[A|B]_U = S_∞(R_AA|R_BB)_{Φ^U} − log|A′|.

> We conjecture that Proposition 10 can be extended to all unitaries with added white noise. We leave this as an open problem.

The preceding paragraph specifies N_p := pR^π + (1 − p)U for p ∈ [0, 1]. The formal statement retains the qubit hypothesis of Proposition 10 and allows arbitrary positive |A′| = |A| = d.

Section II, page 8:

> The Choi state of a bipartite quantum channel N_{A′B′→AB} is Φ^N_{R_AAR_BB} = N(Φ_{R_AA′} ⊗ Φ_{R_BB′}).

Section II.2, page 10:

> D_max(ρ‖σ) = log inf{λ ≥ 0 : ρ ≤ λσ}

> where D_max(ρ‖σ) = +∞ if supp(ρ) ⊄ supp(σ).

Table I, page 11:

> S_∞(A|B)_ρ := −inf_{σ∈St(B)} D_∞(ρ_{AB}‖1_A ⊗ σ_B).

Section V, page 18:

> The Choi operator Γ^N of a bipartite channel N_{A′B′→AB} is Γ^N_{R_AAR_BB} = N(Γ_{R_AA′} ⊗ Γ_{R_BB′}), where Γ_{R_AA′} denotes a maximally entangled operator.

The same section gives S_∞[A|B]_N = −inf_{Q∈Ch(B′,B)} D_∞(Γ^N_{R_AAR_BB}‖1_{R_AA} ⊗ Γ^Q_{R_BB}). Logarithms are to base 2. Density operators and channels are represented by the repository's `DensityState` and `QuantumChannel`; the Choi indices are ordered (R_A, A), (R_B, B).

The proof uses the maximally entangled eigenbasis of a two-qubit state with both marginals maximally mixed, simultaneous sign symmetries of a pure Choi vector and white noise, and pinching of feasible entropy optimizers. The literature screen is recorded in issue #19060; completeness of that screen is ASSUMED-UNVERIFIED.
