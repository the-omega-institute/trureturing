---
bibkey: wuzhongwu2026ghzmeasure
authors: Shengjun Wu; Kaichen Zhong; Jeffery Wu
year: 2026
title: "A measure for genuine tripartite entanglement"
doi: 10.48550/arXiv.2605.02876
url: https://arxiv.org/abs/2605.02876v3
claim: "Equation (37) asks for an analytic proof of the sharp A|BC product-density bound E_GHZ = 1/2."
strata_touched:
  - D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound
license: citation-only
triage: anchor
---

# A measure for genuine tripartite entanglement

S. Wu, K. Zhong and J. Wu, arXiv:2605.02876v3. The following quotations preserve the source's words and formulas with Unicode subscripts and linear notation for displayed fractions.

Section I, printed page 2, equation (1):

> For a unit vector n⃗ ∈ R³, the spin observable on a single qubit is σ_n⃗ = n⃗ · σ = n_x σ_x + n_y σ_y + n_z σ_z, with σ_x, σ_y, σ_z the standard Pauli matrices. For three direction labels n⃗_a, n⃗_b, n⃗_c we denote the tripartite local observable σ(n⃗_a, n⃗_b, n⃗_c) = σ_n⃗_a ⊗ σ_n⃗_b ⊗ σ_n⃗_c, (1) and its expectation ⟨σ(n⃗_a, n⃗_b, n⃗_c)⟩ = Tr[σ(n⃗_a, n⃗_b, n⃗_c)ρ_ABC].

Section V.B, printed page 6, equation (27):

> The fix is to allow each party its own orthonormal frame. Let (â₁, â₂), (b̂₁, b̂₂), (ĉ₁, ĉ₂) be orthonormal pairs on A, B, C, and set I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ) = ⟨σ_â₁ σ_b̂₁ σ_ĉ₁⟩ − ⟨σ_â₁ σ_b̂₂ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₁ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₂ σ_ĉ₁⟩, (27) the natural independent-frame analogue of (2) (here σ_â σ_b̂ σ_ĉ abbreviates σ_â ⊗ σ_b̂ ⊗ σ_ĉ).

Section V.B, printed page 6, equation (30):

> Define the local-unitary invariant measure E_GHZ(ρ) = ½ sup_{â₁⊥â₂, b̂₁⊥b̂₂, ĉ₁⊥ĉ₂} |I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ)|. (30)

Section V.C, printed page 7, equation (37):

> Numerically maximising E_GHZ over all biseparable A|BC states we find the sharp value sup_{ρ ∈ A|BC} E_GHZ(ρ) = ½, (37) attained e.g. by |0⟩_A ⊗ |Φ⁺⟩_BC and coinciding with the product-state value (34); the analytic proof of the exact constant 1/2 remains open. The same 1/2 holds for the B|AC and C|AB partitions by symmetry.

The A|BC class in Section V.C consists of tensor products ρ_A ⊗ ρ_BC with arbitrary density matrices. The formal encoding uses the computational index types Fin 2 and Fin 2 × Fin 2, and the parenthesized tensor index Fin 2 × (Fin 2 × Fin 2). Spin coordinates are real triples with the Euclidean dot product, and orthonormality requires both squared lengths to equal one and their dot product to vanish. Real trace expectations retain the real part explicitly; Hermitian spin observables have real expectations on density matrices.

The exact constant is expressed as a universal upper bound and a density-product attaining it. The attaining state is |0⟩⟨0| ⊗ |Φ⁺⟩⟨Φ⁺|. The result does not establish convexity, property (P6), or the bound for convex mixtures across partitions. Permutation transport to B|AC and C|AB is not formalized here.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2605.02876
- Source: https://arxiv.org/abs/2605.02876v3
