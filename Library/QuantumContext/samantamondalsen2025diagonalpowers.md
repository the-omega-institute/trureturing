---
bibkey: samantamondalsen2025diagonalpowers
authors: M. Samanta; S. Mondal; A. Sen (De)
year: 2025
title: "Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd"
doi: 10.48550/arXiv.2505.18539
url: https://arxiv.org/abs/2505.18539v1
claim: "Appendix B.3 expects equality of multipartite entangling and disentangling powers for arbitrary diagonal unitaries on any number of qubits."
strata_touched:
  - D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers
license: citation-only
triage: anchor
---

# Diagonal-unitary multipartite powers

## Verified locator

DOI: 10.48550/arXiv.2505.18539

Source: https://arxiv.org/abs/2505.18539v1

## Source statements

Page 8, Appendix B.3: “It also indicates that such an equivalence may hold for arbitrary diagonal unitary operators acted on arbitrary number of qubits.”

Page 2, Eq. (1): “E_N(U) = max_{|ψ⟩_FS^N ∈ S_N} G(U|ψ⟩_FS^N)”, where |ψ⟩_FS^N = ⊗_{i=1}^{N} |ψ_i⟩ is fully separable and S_N is the set of fully separable states.

Page 2, Eq. (2): “D_N(U) ≡ E_N(U†) = max_{|ψ⟩_FS^N ∈ S_N} G(U†|ψ⟩_FS^N)”.

Page 6, Appendix A.1: “generalized geometric measure (GGM) which is defined as G(|ψ⟩) = 1 − max_{|ϕ⟩∈S_nG} |⟨ϕ|ψ⟩|², where S_nG denotes the set of all non-genuinely multipartite entangled states.”

## Mathematical encoding

Pure states are complex amplitude functions on `Fin N → Fin 2`. Normalization means the sum of squared moduli is one. Fully separable amplitudes factor into one function per qubit. Biseparable amplitudes factor across a bipartition with both parts nonempty. The overlap is `dotProduct (star φ) ψ`. The maxima in the source are represented by suprema over the corresponding normalized-state subtypes, as specified in issue #19700. Equality follows by conjugation of the two value families and does not require attainment. The statement includes the formal small-system cases N = 0 and N = 1 under these same supremum definitions; the multipartite physical interpretation concerns N ≥ 2.
