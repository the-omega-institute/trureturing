---
bibkey: milekhinadamskapreskill2025observable
authors: Alexey Milekhin; Zofia Adamska; John Preskill
year: 2025
title: "Observable and computable entanglement in time"
doi: null
url: https://arxiv.org/abs/2502.12240v2
claim: "The spacetime density matrix T_AB of subsystems A at time 0 and B at time t is defined by Tr(T_AB (O_A ⊗ 1_B)(1_A ⊗ O_B)) = ⟨O_A(0) O_B(t)⟩ = Tr(ρ O_A U† O_B U) (Eqs. (4), (9)); its partial traces are the reduced density matrices (Eq. (15)). Conjecture 1 asserts the analogue of Audenaert's inequality, 1 + ||T_AB||_p ≥ ||Tr_A T_AB||_p + ||Tr_B T_AB||_p for every finite-dimensional T_AB and p > 1 (Eq. (25)), with the Schatten norm ||M||_p = (Tr (M†M)^{p/2})^{1/p} (footnote a)."
strata_touched:
  - D5/S3/Quantum/Information/SpacetimeDensitySchattenSubadditivityRefutation
license: citation-only
triage: anchor
---

# Milekhin, Adamska and Preskill, observable and computable entanglement in time

A. Milekhin, Z. Adamska and J. Preskill, *Observable and computable entanglement in time*, arXiv:2502.12240 [quant-ph] (v2 of 14 December 2025; v1 of 17 February 2025).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2502.12240v2

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2502.12240v2:
- p. 2, Eqs. (4)–(9), the definition of the spacetime density matrix;
- p. 4, §IV items 1–9, footnote a, Theorem 1 (Audenaert), Conjecture 1 (Eq. (25)) and Theorem 2.

## Source statements

Eq. (4) and the following text (p. 2): "⟨O_A(0)O_B(t)⟩ = Tr(ρO_A U†O_B U), (4) where U may be interpreted as a unitary time evolution operator. Now A and B represent parts of the system at different times. They do not have to be related to each other in any particular way."

Eq. (9) (p. 2): "Tr(T_AB (O_A ⊗ 1_B)(1_A ⊗ O_B)) = ⟨O_A(0)O_B(t)⟩. (9) This property can be taken as the definition of T_AB."

Footnote a (p. 4): "The Schatten p-norm of a matrix M is defined as ||M||_p = (Tr (M†M)^{p/2})^{1/p}."

§IV, item 9 (p. 4): "Audenaert has proven [22] subadditivity of p > 1 Rényi entropies in the following form: Theorem 1 (Audenaert) For any density matrix ρ_AB on a finite-dimensional Hilbert space H_A ⊗ H_B and p > 1: 1 + ||ρ_AB||_p ≥ ||Tr_A ρ_AB||_p + ||Tr_B ρ_AB||_p. (24) We have obtained some numerical evidence that T_AB satisfies the same inequality, so we will formulate it as a conjecture: Conjecture 1 For any T_AB on a finite-dimensional H_A ⊗ H_B and p > 1: 1 + ||T_AB||_p ≥ ||Tr_A T_AB||_p + ||Tr_B T_AB||_p. (25) In App. D we prove a special case of this statement: Theorem 2 Suppose that the initial state ρ = |ψ_Ā⟩⟨ψ_Ā| ⊗ ρ_A. Then for any p > 0, ||T_AB||_p ≥ ||Tr_A T_AB||_p = ||ρ_B||_p. (26)"

## Reading used by the repository

The whole system is H_A ⊗ H_Ā at time 0 and H_B ⊗ H_B̄ at time t, and U is a unitary between these two factorizations. T_AB is any matrix on H_A ⊗ H_B satisfying Eq. (9) for all O_A and O_B; this determines T_AB uniquely. Tr_A and Tr_B are the partial traces over the two factors. Conjecture 1 is read as the inequality (25) for every finite dimension, every density matrix ρ, every such U and every real p > 1.
