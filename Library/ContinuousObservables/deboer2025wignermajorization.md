---
bibkey: deboer2025wignermajorization
authors: Jan de Boer, Giuseppe Di Giulio, Esko Keski-Vakkuri, Erik Tonni
year: 2025
title: "Continuous majorization in quantum phase space for Wigner-positive states and proposals for Wigner-negative states"
doi: 10.1103/w561-h3z5
url: https://arxiv.org/abs/2412.19698v3
claim: "The vacuum/one-photon mixtures form a Wigner-majorization chain increasing on [1/2,1] and decreasing on [0,1/2] under Proposal 1."
strata_touched:
  - D5/S3/Analytic/Convexity/DerivativeHingeMajorization
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/VacuumOnePhotonWignerMajorization
license: citation-only
triage: anchor
---

# Wigner-majorization chains for vacuum and one-photon mixtures

## Verified locator

DOI: 10.1103/w561-h3z5

Source: https://arxiv.org/abs/2412.19698v3

The journal publication is Physical Review A 112, 032405. The cited arXiv version is v3. Its PDF numbers the level functional, threshold comparison, Fock Wigner function and mixture as Eqs. (97), (98), (99) and (100), respectively.

## Source statements

Page 16, Eq. (99): “W_{|n⟩}(x,p) = ((−1)ⁿ/π) e^{−(x²+p²)} Lₙ(2(x²+p²))”. Eq. (100): “W̃_u(r) = (1 − u) W_{|0⟩}(r) + u W_{|1⟩}(r)”, with “u ∈ [0, 1]”. Eq. (97): “I_t[|W_ρ̂|] ≡ ∫ [|W_ρ̂(r)| − t]₊ dr”.

Page 16, Result 8: “We define that ρ̂₁ ≻_W ρ̂₂ if and only if |W₁| ≻_w |W₂|”. Eq. (98) is the comparison of the level functionals for every t ≥ 0.

Page 17, Section V.A.1: “By trying for several instances, we may conjecture that there is a majorization order along the family W̃_u only as long as u > 1/2.” “It would be interesting to understand this observation better analytically. We leave this question for future works.”

## Mathematical scope

The proposition in issue #18571 specifies increasing order on [1/2,1] and decreasing order on [0,1/2], including both endpoints. These are assertions about Proposal 1. The Laguerre polynomial is the existing genLaguerre 0 n; the level functional is the real Bochner integral over product Lebesgue measure on ℝ × ℝ.

The general cancellation theorem assumes a continuous profile with an everywhere derivative, an integrable derivative, a nonnegative derivative before a nonnegative peak location, a nonpositive derivative afterwards, and zero endpoint limits. The convex minimum requires the profile to be nonnegative and both profile and derivative to be integrable. The concrete profile is h(s)=s exp(−s). Strictness, complete cross-branch classification and cancellation for general non-unimodal absolutely continuous profiles are outside these statements.

The experiment is in the-omega-institute/trureturing-experiments at commit fec5519e820aa7ae835e09692fb27fdccb2f49b7, path docs/reports/deboer-digiulio-keskivakkuri-tonni-2025-vacuum-one-photon-wigner-majorization/check.py, SHA-256 26165b657205c4f6d509c5a79fbaa3a07a13ecab3c2a79a61cbe378b33b5cfd8. Its reported exit code is 0, with 8610 comparisons on each branch and no violations. Numerical comparisons are distinct from the universal Lean proposition.

The literature screen in #18571 includes the source versions, the Wigner-positive vacuum result of Van Herstraeten–Jabbour–Cerf and the different preorder of Upadhyaya et al. Its completeness is ASSUMED-UNVERIFIED.
