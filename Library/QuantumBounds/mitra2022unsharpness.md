---
bibkey: mitra2022unsharpness
authors: Arindam Mitra
year: 2022
title: "Quantifying unsharpness of observables in an outcome-independent way"
doi: 10.1007/s10773-022-05219-2
url: https://arxiv.org/abs/2201.02578v3
claim: "For an observable A = {A_i}, the X-matrix is X^A = Σ_i ‖A_i‖A_i and the instrument-independent unsharpness measures are E(A) = ‖I − X^A‖ and E′(A) = Tr[(I/d)(I − X^A)]. Theorems 3–4 show that E and E′ are non-decreasing under the white noise A^λ_i = λA_i + (1 − λ)I/n exactly when Σ^A_1 ≥ Σ^A_2 and Σ′^A_1 ≥ Σ′^A_2, respectively; Propositions 1–2 prove both for dichotomic qubit observables, and Conjecture 1 asserts both for every qubit observable."
strata_touched:
  - D5/S3/Quantum/Measurements/MitraUnsharpnessWhiteNoiseRefutation
license: citation-only
triage: anchor
---

# Mitra, quantifying unsharpness of observables in an outcome-independent way

A. Mitra, *Quantifying unsharpness of observables in an outcome-independent way*, Int. J. Theor. Phys. **61**, 236 (2022), DOI 10.1007/s10773-022-05219-2; arXiv:2201.02578 [quant-ph] (v3, the latest of versions v1–v3).

## Verified locator

DOI: 10.1007/s10773-022-05219-2 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2201.02578v3.
Source: https://arxiv.org/pdf/2201.02578v3 (text read from the PDF):
- §IV.A, the measures E and E′ (Eqs. (44) and (48));
- §IV.B, Theorems 3–4, Eqs. (50)–(62), and Propositions 1–2;
- §IV.B, page 11, Conjecture 1;
- §VII, the request to prove Conjecture 1.

## Source statements

Theorem 3: "Suppose A^λ = {A^λ_i}^{n_A}_{i=1} is an unsharp version of A = {A_i}^{n_A}_{i=1} i.e., A^λ_i = λA_i + (1 − λ) I/n_A for all i ∈ {1, ..., n_A} where 1 ≥ λ ≥ 0. Then E(A^λ) ≥ E(A) for all 1 ≥ λ ≥ 0 iff Σ^A_1 ≥ Σ^A_2 (50) holds where Σ^A_1 = (⟨x^A_min| X^A |x^A_min⟩ − 1/n_A) and Σ^A_2 = (Σ_i ‖A_i‖/n_A − ⟨x^A_min| X^A |x^A_min⟩) where x^A_min is the lowest eigen value of X^A and |x^A_min⟩ is the eigen state of X^A corresponding to the eigen value x^A_min."

Theorem 4: the same for E′, "iff Σ′^A_1 ≥ Σ′^A_2 (60) holds where Σ′^A_1 = (1/d)Tr[X^A] − 1/n and Σ′^A_2 = Σ_i ‖A_i‖/n_A − (1/d)Tr[X^A]."

Page 11: "We have searched for examples for which inequality (50) inequality (60) do not hold. But we could not find any such example. Noting these facts, we provide the following conjecture-
Conjecture 1. For any qubit observable A, inequality Σ^A_1 ≥ Σ^A_2 and inequality Σ′^A_1 ≥ Σ′^A_2 hold and therefore, E(A^λ) ≥ E(A) and E′(A^λ) ≥ E′(A) for all 1 ≥ λ ≥ 0."

§VII: "It would be interesting to prove Conjecture 1 in the future."

## Reading used by the repository

A qubit observable with n outcomes is a family of n positive semidefinite 2 × 2 complex matrices summing to the identity, for any n ≥ 1. The norm ‖·‖ is the operator norm, and x^A_min is the lowest eigenvalue of the Hermitian matrix X^A. E(A) = ‖I − X^A‖ as in Eq. (44), and E′(A) = Tr[(I/2)(I − X^A)] as in Eq. (48) with d = 2. The conjecture is read as the conjunction of its four clauses for every qubit observable.
