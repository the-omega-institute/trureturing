---
bibkey: zhengliu2024magicdistillationdynamics
authors: Yunzhe Zheng; Dong E. Liu
year: 2025
title: "From Magic State Distillation to Dynamical Systems"
doi: 10.22331/q-2025-09-15-1858
url: https://arxiv.org/abs/2412.04402v2
claim: "For a stabilizer code with stabilizer elements s_j and logical operators Z̄_i, if every s_j Z̄_i contains a Pauli Z tensor factor then z = 0 is a fixed plane of the distillation map (Proposition 3, Eq. (23)); the authors conjecture that this condition can be met for any stabilizer code by choosing the logical Z operators."
strata_touched:
  - D5/S3/Quantum/Information/StabilizerLogicalZSupportRefutation
license: citation-only
triage: anchor
---

# Zheng and Liu, magic state distillation as a dynamical system

Y. Zheng and D. E. Liu, *From Magic State Distillation to Dynamical Systems*, Quantum **9**, 1858 (2025), DOI 10.22331/q-2025-09-15-1858; arXiv:2412.04402 [quant-ph] (v1 5 December 2024; v2, accepted in Quantum 9 September 2025).

## Verified locator

DOI: 10.22331/q-2025-09-15-1858 (Crossref: Quantum 9, article 1858, published 15 September 2025; the v2 footer reads "Accepted in Quantum 2025-09-09").
Primary version read: https://arxiv.org/abs/2412.04402v2; the text was read from the PDF.
- §2: Eqs. (3)–(6), the codespace projector and the logical output coordinates;
- §3: Eqs. (12)–(15), the Pauli-weight form of the success probability, and Proposition 3 with Eq. (23) and the conjecture after it.

The same conjecture sentence appears in v1. The journal typesetting was not compared line by line.

## Source statements

§2: "P_Q = ∏_{i=1}^{n̄} (I + g_i)/2 = (1/2^{n̄}) Σ_{i=1}^{2^{n̄}} s_i. (3)", with n̄ = n − k, and "x^o_i = Tr[P_Q ρ_in X̄_i]/p_s, y^o_i = Tr[P_Q ρ_in Ȳ_i]/p_s, z^o_i = Tr[P_Q ρ_in Z̄_i]/p_s (6)".

§3: "s_j = (−1)^{α_j} s^1_j ⊗ s^2_j ⋯ ⊗ s^n_j, (13) where α_j ∈ {0, 1} and s^l_j ∈ {I, X, Y, Z}", and "Tr[s_j ρ^{⊗n}] = (−1)^{α_j} x^{w^X_j} y^{w^Y_j} z^{w^Z_j}, (14) where w^X_j, w^Y_j, w^Z_j are separately the weight of X, Y, Z in stabilizer operator s_j."

§3, Proposition 3: "For a stabilizer code Q, z = 0 is a fixed plane in the mapped dynamical system if s_j Z̄_i explicitly contains Pauli Z operators for every logical operator Z̄_i (i = 1, ..., k) and every stabilizer element s_j (j = 1, ..., 2^n̄). If each s_j Z̄_i contains at least one Pauli Z, then T^z_i(x, y, z) = z · T̃^z_i(x, y, z) (23). Therefore, T^z_i(x, y, 0) = 0, which means z = 0 is a fixed plane for the system. This condition is satisfied by most known protocols that we have examined and we conjecture it to be generally true for any stabilizer codes by properly choosing the logical Z operators without modifying the stabilizer groups."

## Reading used by the repository

Pauli words are taken modulo phase. A tensor factor counts as "Pauli Z" only when it is Z: by Eq. (14), a Y factor contributes y, not z. A stabilizer code is given by pairwise commuting, independent generator words with fewer generators than qubits. The conjecture is read as the existence, for every such code, of a nontrivial logical word L (commuting with the generators and not in the stabilizer group) such that every product s·L with s in the stabilizer group has a Z factor. For k ≥ 2 this asks for one logical operator only, which the conjecture implies.
