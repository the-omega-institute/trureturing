---
bibkey: saleem2025curvature
authors: Zain H. Saleem; Anil Shaji; Anjala M. Babu; Da-Wei Luo; Quinn Langfitt; Ting Yu; Stephen K. Gray
year: 2025
title: Quantum Fisher Information and the Curvature of Entanglement
doi: 10.48550/arXiv.2504.13729
url: https://arxiv.org/abs/2504.13729
claim: "Section IV.B conjectures CoE ≤ QFI for the amplitude-damped two-qubit evolution (41), with equality at specific points."
strata_touched:
  - D5/S3/Quantum/Information/SaleemNoisyCurvatureRefutation
license: citation-only
triage: anchor
---

# Quantum Fisher Information and the Curvature of Entanglement

## Verified locator

DOI: 10.48550/arXiv.2504.13729

Source: https://arxiv.org/abs/2504.13729

The quotations and page numbers refer to arXiv:2504.13729v4, https://arxiv.org/pdf/2504.13729v4.

## Source statements

Section IV.B, page 9: “For the case with decay also there are more general examples we can consider but in all cases we conjecture that CoE ≤ QFI with equality at specific points.”

Section II, page 3: “the λi are the square roots of the eigenvalues, in decreasing order, of the matrix R = ρ(σy ⊗ σy)ρ∗(σy ⊗ σy).” The same paragraph defines concurrence by max(0, λ1 − λ2 − λ3 − λ4); equation (7) defines CoE ≡ −∂g² C(ρ).

Section II, page 2, defines the Hermitian symmetric logarithmic derivative by ∂gρ=(ρL+Lρ)/2 and QFI by Tr(ρL²).

Equation (41), page 8, evolves the two-qubit probe by −i[Hprobe,ρ] + κ Σj D[σ₋⁽ʲ⁾](ρ), where D[O](ρ)=OρO†−(O†Oρ+ρO†O)/2. Equation (21) supplies the flip-flop Hamiltonian with ηxy=1. Appendix B fixes σ₋=(σx−iσy)/2=|1⟩⟨0|. Equations (42)–(43) describe particular noisy probes; they do not quantify over all initial density matrices.

## Scope

The lossless result in Section III.B assumes a pure initial probe. Section III explicitly introduces the more general case with losses and mixed initial states. The noisy conjecture is compared at smooth concurrence points, excluding its singularities.

The repository refutation uses the parameter-independent initial density matrix diag(1,11,3,1)/16 and the positive-damping point t=1, κ=log 2, g=π/4. There CoE=1 and QFI=8/15. The proof concerns this explicit point; the counterfamily for every positive κ and t is a separate computed result.
