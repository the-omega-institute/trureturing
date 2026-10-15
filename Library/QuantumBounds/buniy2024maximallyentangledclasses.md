---
bibkey: buniy2024maximallyentangledclasses
authors: Roman V. Buniy, Robert P. Feger, Thomas W. Kephart
year: 2024
title: "Decoherence and the classes of maximally entangled states"
doi: 10.1142/S0219749924500357
url: https://arxiv.org/abs/2210.07618v1
claim: "A maximally entangled state of an n-partite system is a state at which every algebraic entanglement invariant (kernel dimensions of the flattenings and contraction maps built from its coordinates; for n = 3 the four invariants of Appendix A) takes its least value, and these states form the maximally entangled class C_D. The length of a state is its number of nonzero coordinates in a product basis, and L_D is the least length in C_D. From exact values for 3-partite dimensions up to 5 (Table XII) the authors conjecture L_(d₁,d₂,d₃) = d₁ + d₂ + d₃ − 2 when min(d₁, d₂, d₃) ≥ 3 (Conjecture III.4)."
strata_touched:
  - D5/S3/Quantum/Entanglement/TripartiteMaximalClassLengthRefutation
license: citation-only
triage: anchor
---

# Buniy–Feger–Kephart, decoherence and the classes of maximally entangled states

R. V. Buniy, R. P. Feger and T. W. Kephart, *Decoherence and the classes of maximally entangled states*, Int. J. Quantum Inf. **22**, 2450035 (2024), DOI 10.1142/S0219749924500357; arXiv:2210.07618 [quant-ph] (v1, the only arXiv version).

## Verified locator

DOI: 10.1142/S0219749924500357 (as listed by Crossref, published July 2024).
Primary version read: https://arxiv.org/abs/2210.07618v1. The journal text was not read.
Source: https://arxiv.org/pdf/2210.07618v1 (text read from the PDF):
- §II.A, Definition II.1 (maximally entangled states and the maximally entangled class);
- §III, Eq. (2) (the length L(v) and L_D);
- §III.C, Table XII and Conjecture III.4;
- Appendix A, Theorem A.1 and Eqs. (A1)–(A6) (the invariants n₁, n₂, n₃, n₁,₂,₃ for n = 3).

## Source statements

Definition II.1: "A maximally entangled state (MES) of an n-partite system with the dimensions D = (d₁, …, d_n) is any state v for which every invariant in the set N_D(v) takes its least possible value. The set of all maximally entangled states is the maximally entangled class (MEC) C_D."

Appendix A: "The algebraic invariants are N = (n₁, n₂, n₃, n₁,₂,₃), where n_i = dim K_i, 1 ≤ i ≤ 3 and n₁,₂,₃ = dim K₁,₂,₃."

Conjecture III.4: "The shortest length of states in an MEC for n = 3 is L_(2,d₂,d₂) = 2d₂ − 2, L_(2,d₂,d₃) = 2d₂ for d₂ < d₃ and L_(d₁,d₂,d₃) = Σ_{i=1}^{3} d_i − 2 for min(d₁, d₂, d₃) ≥ 3."

## Reading used by the repository

A state is a coefficient array v_{ijk} in the product basis.
- K₁ = {w : Σ_i v_{ijk}w_i = 0 for all j, k}, and K₂, K₃ likewise for the second and third factors (Eqs. (A1)–(A3); the printed (A3) writes w_j for w_k).
- K₁,₂,₃ is the space of arrays z with Σ_{j,k} v_{ajk}z_{bjk} = 0, Σ_{i,k} v_{iak}z_{ibk} = 0 and Σ_{i,j} v_{ija}z_{ijb} = 0 for all indices a, b (Eqs. (A4)–(A6)).
- The class C_D is the set of states at which all four dimensions are minimal over all states.
