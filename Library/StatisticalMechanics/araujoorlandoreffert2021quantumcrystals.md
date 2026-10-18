---
bibkey: araujoorlandoreffert2021quantumcrystals
authors: Thiago Araujo; Domenico Orlando; Susanne Reffert
year: 2021
title: "Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality"
doi: 10.1103/PhysRevD.103.026020
url: https://arxiv.org/abs/2005.09103v2
claim: "The quantum crystal melting Hamiltonian H = −J(Γ + Π) + V(√q O₊ + O₋/√q) acts on plane-partition states; a fermion-boson correspondence (46) defines bosonic states through symmetric-group characters, and Section VI conjectures that Γ, Π and O± are linear combinations of the affine Yangian Y[gl̂(1)] generators, with the bosonic states forming its MacMahon representation, so that O± lie in the Cartan part B."
strata_touched:
  - D5/S3/StatisticalMechanics/QuantumCrystalYangianRefutation
license: citation-only
triage: anchor
---

# Araujo, Orlando and Reffert, quantum crystals and plane partitions

T. Araujo, D. Orlando and S. Reffert, *Quantum crystals, Kagome lattice, and plane partitions fermion-boson duality*, Phys. Rev. D 103, 026020 (2021), DOI 10.1103/PhysRevD.103.026020; arXiv:2005.09103 [hep-th] (v1 18 May 2020, v2 27 January 2021).

## Verified locator

DOI: 10.1103/PhysRevD.103.026020

Source: https://arxiv.org/abs/2005.09103v2; the text was read from the PDF.
- page 2: the Hamiltonian, Eqs. (2a)–(2b), and the meaning of Γ, Π and O±;
- page 8: the fermion-boson correspondence, Eqs. (42)–(46), the conjecture of Section VI and Eqs. (49)–(50);
- page 9: the consequence O± ∈ B and Eq. (51);
- page 10: the character table (A13);
- pages 11–12: Appendix C, the basis transformation for at most three boxes.

## Source statements

Eq. (2b): "H = −J (Γ + Π) + V (√q O+(Π, Γ) + (1/√q) O−(Π, Γ)) … the operator Γ (Π) adds (removes) boxes in all possible ways. Moreover, the potential terms O+(Π, Γ) and O−(Π, Γ) count the number of positive and negative flippable plaquettes, respectively." A negative flip removes a box from the plane partition.

Eq. (46): "|Λ(N K)⟩⟩ = Σ_Λ χ_Λ[C(K)] |Λ⟩", where χ_Λ is the product over layers of characters of symmetric groups (Eq. (42c)), and "the correspondence between the plane partition basis preserves the number of boxes grading".

Conjecture (Section VI): "The growth operators Γ, Π and O±(Γ, Π) are linear combinations of the generators of the algebra Y[gl̂(1)], and the states |N K⟩⟩ fulfill the Y[gl̂(1)] MacMahon representation."

Eqs. (49)–(50): "e_j|Λ⟩⟩ = Σ_{□∈Q+} E_j(Λ ↦ Λ + □)|Λ + □⟩⟩, f_j|Λ⟩⟩ = Σ_{□∈Q−} F_j(Λ ↦ Λ − □)|Λ − □⟩⟩. … the operators ϕ_j act diagonally as ϕ_j|Λ⟩⟩ = ϕ_{j,Λ}|Λ⟩⟩."

Page 9: "if the conjectured correspondence between the generators of Y[gl̂(1)] and with the growth operators Γ and Π is indeed correct, we immediately conclude that O±(Π, Γ) ∈ B since they can be written as linear combinations of ϕ_j."

Character table (A13), S₃: χ₍₁,₁,₁₎, χ₍₂,₁₎, χ₍₃₎ take the values 1, 2, 1 on the identity class (3, 0, 0, …). Appendix C, Eq. (C2b), writes the corresponding bosonic state as the single-layer combination of the column, twice the hook, and the row.

## Reading used by the repository

The state space has the plane partitions as basis, graded by the number of boxes, and O₋ acts on it diagonally by the number of removable boxes. The bosonic state of the identity class of S₃ is v = |(3)⟩ + 2|(2, 1)⟩ + |(1, 1, 1)⟩, by Eq. (46) with (A13) and as written in Appendix C. The repository refutes the consequence of the conjecture at v: a linear combination of operators satisfying (49)–(50) at v cannot agree with O₋ on v.
