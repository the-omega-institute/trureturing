---
bibkey: khareletal2026pseudoentropy
authors: Pramod Kamal Kharel; Manghang Limbu; Nabaraj Khatri; Ashish Khanal; Kiran Adhikari
year: 2026
title: "Pseudo entropy and topological phases of matter"
doi: null
url: https://arxiv.org/abs/2606.29311v1
claim: "For pure states |ψ⟩, |φ⟩ with ⟨φ|ψ⟩ ≠ 0, the transition matrix is T = |ψ⟩⟨φ|/⟨φ|ψ⟩, the reduced transition matrix is T_A = Tr_B T, and the pseudo entropy is S(T_A) = −Tr(T_A log T_A) (Eqs. (1)–(3)); the averaged excess entropy is ∆S = Re S(T_A) − (S(ρ_A^ψ) + S(ρ_A^φ))/2 (Eq. (21)). For half-filled ground states of the periodic SSH Hamiltonian (Eq. (15)) at w = 1 in the same phase, the authors report that the conjectured non-positivity ∆S ≤ 0 holds and state in §VI that under periodic boundary conditions it is fully satisfied with no exceptions at all system sizes."
strata_touched:
  - D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
license: citation-only
triage: anchor
---

# Kharel, Limbu, Khatri, Khanal and Adhikari, pseudo entropy and topological phases of matter

P. K. Kharel, M. Limbu, N. Khatri, A. Khanal and K. Adhikari, *Pseudo entropy and topological phases of matter*, arXiv:2606.29311 [cond-mat.stat-mech] (v1 of 28 June 2026, the only version listed).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2606.29311v1

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2606.29311v1:
- p. 2, §II, Eqs. (1)–(5), the transition matrix and the pseudo entropy;
- pp. 3–4, Eqs. (13)–(17), the SSH Hamiltonian with open and periodic boundary conditions and its phases;
- p. 5, §IV, Eq. (21) and the setup of the non-positivity test;
- p. 9, §VI, the conclusion.

## Source statements

Eqs. (1)–(3) (p. 2): "T^{ψ|φ} = |ψ⟩⟨φ| / ⟨φ|ψ⟩, (1) … the reduced transition matrix of system A is defined by tracing out the system B, T_A^{ψ|φ} ≡ Tr_B[T^{ψ|φ}] = Tr_B[|ψ⟩⟨φ| / ⟨φ|ψ⟩]. (2) and pseudo entropy is defined as: S(T_A^{ψ|φ}) = −Tr[T_A^{ψ|φ} log T_A^{ψ|φ}]. (3)"

Eq. (15) (p. 4): "For Periodic Boundary Condition (PBC), we connect the last unit cell to the first one, c_{N+1,A} ≡ c_{1,A}, and the Hamiltonian is: Ĥ_PBC = v Σ_{m=1}^{N} (c†_{m,B} c_{m,A} + h.c.) + w Σ_{m=1}^{N} (c†_{m+1,A} c_{m,B} + h.c.), (15)"

§IV (p. 5): "∆S(T_A^{ψ|φ}) = Re[S(T_A^{ψ|φ})] − ½ (S(ρ^ψ)_A + S(ρ^φ)_A) (21) … In [25, 26], it was conjectured that the averaged excess entropy is non-positive, ∆S(T_A^{ψ|φ}) ≤ 0, when the states |ψ⟩ and |φ⟩ are in the same phase. … We consider two SSH Hamiltonians (15) Ĥ(v1, w) and Ĥ(v2, w) with fixed w = 1, and denote their half-filled ground states by |Ψ1⟩ ≡ |Ψ(v1)⟩ and |Ψ2⟩ ≡ |Ψ(v2)⟩."

§VI (p. 9): "Under periodic boundary conditions, the conjecture is fully satisfied with no exceptions at all system sizes and across all three phases: topological, trivial, and crossing."

## Reading used by the repository

The Fock space of the 2N modes (1,A), (1,B), …, (N,A), (N,B) carries Jordan–Wigner annihilation operators in this order, and Ĥ_PBC(v) = Σ h_ij c_i† c_j with h the single-particle matrix of Eq. (15) at w = 1. A half-filled ground state is a nonzero N-particle vector of minimal energy in the N-particle sector. A is the first L unit cells, and Tr_B is the partial trace over the remaining modes. The entropy of a matrix is −Σ λ log λ over its eigenvalues with multiplicity. The §VI assertion is read as: for every N ≥ 2, every L with 1 ≤ L < N, and all v1, v2 in the same phase, ∆S ≤ 0.
