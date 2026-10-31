---
bibkey: campoamor2026zernike
authors: R. Campoamor-Stursberg, F. J. Herranz, D. Latini, I. Marquette, A. Blasco
year: 2026
title: "Generalized quantum Zernike Hamiltonians: Polynomial Higgs-type algebras and algebraic derivation of the spectrum"
doi: 10.1088/1361-6544/ae64a2
url: https://arxiv.org/abs/2502.02491v2
claim: "Conjecture 1(iii) asserts the existence of number and ladder operators with the factorized structure function (5.1) for every order N."
strata_touched:
  - D5/S3/Quantum/CampoamorStursbergZernikeLadderCore
  - D5/S3/Quantum/CampoamorStursbergZernikeLadder
license: citation-only
triage: anchor
---

# Generalized quantum Zernike ladders

## Verified locator

DOI: 10.1088/1361-6544/ae64a2

Source: https://arxiv.org/abs/2502.02491v2

Nonlinearity 39 (2026), 055008. The locator is the published-version arXiv revision v2, 24 April 2026.

## Source statement

Page 19, Conjecture 1(iii): “The set (Ĉ, Î_N, Î'_N) leads to the quantum symmetries K̂₁, K̂₂, K̂₃ in (2.8) and, in consequence, it is possible to define the number and ladder operators K̂, K̂₊, K̂₋ verifying the commutation relations (2.9) with the structure function Φ = Φ₁Φ₂ (2.10), whose factorizing terms are given by Φ₁(Ĥ_N, K̂) = ¼ (Ĥ_N − Σ_{k=1}^N (2i)^k γ_k K̂^k), Φ₂(Ĥ_N, K̂) = Ĥ_N − Σ_{k=1}^N (−2i)^k γ_k (K̂ − Id)^k. (5.1)”

Equations (2.1), (2.3), (2.5)–(2.10) define the coordinate and momentum realization, Hamiltonian, angular momentum, correction monomials, symmetries and generated algebra. Source coordinates 1 and 2 are encoded as Fin 2 indices 0 and 1. Operators act on complex polynomial wavefunctions. The coefficient sequence is arbitrary complex data, with only indices 1 through N used. The correction span consists of normal-ordered monomials of positive degree at most 2N and grading zero.

The proved proposition supplies two symmetries of this form commuting with the Hamiltonian and three elements of their generated algebra satisfying (2.9) and the factorization (5.1). It asserts the momentum-order upper bound, and makes no exact-order assertion for degenerate coefficients. Algebraic independence in Conjecture 1(ii) and the spectral questions of Conjecture 2 remain open here.

The literature screen in issue #19957 inspected the source, the same-author review arXiv:2511.09541v1, arXiv:2605.23748v2 and arXiv:2504.15713v1 without finding a settlement of the arbitrary-order quantum factorization. Completeness is ASSUMED-UNVERIFIED.

The symbolic experiment is in the-omega-institute/trureturing-experiments, commit 9f3dcb3b, docs/reports/campoamor-stursberg-et-al-2025-zernike-ladder-factorization/check.py; source SHA-256 e158a68aaeff7c4699928ed1e85a19c857f179f8c392ff381c44f88e1d36d72e. Its recorded exit code is 0; out.txt has SHA-256 b25971e40e831642e14566194ea65e53439145374d74007ca374b01baa118219. These finite symbolic checks are separate from the arbitrary-order Lean proof.
