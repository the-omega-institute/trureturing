---
bibkey: litan2024bargmann
authors: Mao-Sheng Li; Yi-Xi Tan
year: 2024
title: On the Bargmann invariants for quantum imaginarity
doi: 10.48550/arXiv.2412.08022
url: https://arxiv.org/abs/2412.08022v1
claim: Section III conjectures that the circulant formed from geometric means of moduli and arithmetic means of principal phases preserves positive semidefiniteness of correlation matrices in general dimension.
strata_touched:
  - D5/S3/Quantum/Matrix/LiTanCirculantPositivityRefutation
license: citation-only
triage: anchor
---

# Li and Tan: circulant positivity

## Verified locator

DOI: 10.48550/arXiv.2412.08022

Source: https://arxiv.org/abs/2412.08022v1

## Source statements

Section II, page 2: “Let 𝐇_n denote the set of all n × n Hermitian matrices H that are positive semidefinite and have h_ii = 1 for all i = 1, …, n.”

Section II, page 2: “Let C_n = G_{(0,1,0,…,0)}”. Its displayed matrix has ones on the superdiagonal and in the bottom-left corner.

Section III, page 5: “For each H = (h_kl) ∈ Mat_{n×n}(ℂ), we can associate it with a circulant matrix C_H = Σ_{k=0}^{n−1} z_k C_nᵏ, where the coefficients are given by z_k = (Π_{l=1}^n r_{l(l⊕k)})^{1/n} e^{iθ_k}, with θ_k := (Σ_{l=1}^n θ_{l(l⊕k)})/n and h_kl = r_kl e^{iθ_kl}, where r_kl ≥ 0 and θ_kl ∈ (−π, π].”

Section III, page 5: “For the case when n = 3, we deduced that the positive semidefiniteness of C_H follows from the positive semidefiniteness of H. This leads us to the conjecture that the positive semidefiniteness of H implies the positive semidefiniteness of C_H (which may depend on n) for general n.”

## Encoding and scope

Indices are `Fin n`, with addition modulo n. The phase is `Complex.arg`, the modulus is the complex norm, and the root is `Real.rpow` of the nonnegative product. The source's shift is written directly in the sum defining `CH`. The conjecture is restricted to positive semidefinite matrices with unit diagonal; a counterexample in this smaller class refutes the assertion for unrestricted positive semidefinite matrices as well.

The repository refutation uses the real rational matrix with rows
`(1,5/8,1/9,5/8)`, `(5/8,1,5/8,4/9)`, `(1/9,5/8,1,5/8)`, and `(5/8,4/9,5/8,1)`.
A diagonal Gram factorization proves positivity. The transformed first row is
`(1,5/8,2/9,5/8)`, and the quadratic value at `(1,−1,1,−1)` is `−1/9`.
The parameterized family and the source's n = 3 assertion are outside this Lean theorem.

Literature completeness and agreement of the journal version, Phys. Rev. A 111 (2025) 022409, with this arXiv statement are ASSUMED-UNVERIFIED.
