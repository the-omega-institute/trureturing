---
bibkey: ortheyphilipkondrastreltsov2026optimality
authors: Alexandre C. Orthey; Aby Philip; Tulja Varun Kondra; Alexander Streltsov
year: 2026
title: "Optimality of universal conclusive entanglement concentration protocols"
doi: 10.1103/bz3j-9njg
url: https://arxiv.org/abs/2509.09423v2
claim: "Definition 1: an n-to-1 LOCC map E1 is a universal conclusive entanglement concentration protocol if ⟨ϕ+|E1(ρ⊗n)|ϕ+⟩ = Tr E1(ρ⊗n) for every ρ in the input set. For four copies of an arbitrary two-qubit pure state c1|00⟩ + c2|01⟩ + c3|10⟩ + c4|11⟩ (Eq. (1)), Theorem 3 bounds the success probability of concatenated protocols based on two-qubit operations by 2|c2⁴c3⁴| + 2|c1⁴c4⁴| − 4Re[c1²c4²(c2*)²(c3*)²] (Eq. (8)), and §VIII conjectures that protocols processing four copies directly cannot surpass this bound."
strata_touched:
  - D5/S3/Quantum/PureState/FourCopyConcentrationRefutation
license: citation-only
triage: anchor
---

# Orthey, Philip, Kondra and Streltsov, optimality of universal conclusive entanglement concentration

A. C. Orthey, A. Philip, T. V. Kondra and A. Streltsov, *Optimality of universal conclusive entanglement concentration protocols*, Phys. Rev. A 113, 062404 (2026); arXiv:2509.09423 [quant-ph] (v2 of 3 June 2026; v1 of 11 September 2025, titled "… entanglement purification protocols").

## Verified locator

DOI: 10.1103/bz3j-9njg

Source: https://arxiv.org/abs/2509.09423v2

The arXiv record lists the journal reference Phys. Rev. A 113, 062404 (2026) and the DOI 10.1103/bz3j-9njg. The text was read from the PDF https://arxiv.org/pdf/2509.09423v2:
- p. 2: §II, Definitions 1 and 2;
- pp. 2–3: §IV, Eq. (1);
- p. 3: §VI, Theorem 3 and Eq. (8);
- p. 6: §VIII, the conjecture.

## Source statements

Definition 1 (p. 2): "Let S be the subset of states ρ that are shared between Alice and Bob. The n-to-1 map E1 is called a universal conclusive ECP for a given number of copies n if, for every ρ ∈ S, it holds that ⟨ϕ+|E1(ρ⊗n)|ϕ+⟩ = Tr E1(ρ⊗n)." Here E1 and E2 are completely positive trace non-increasing LOCC maps with E1 + E2 trace preserving.

§IV (p. 2): S is the set of all pure two-qubit states, "|ψ⟩ = c1|00⟩ + c2|01⟩ + c3|10⟩ + c4|11⟩, (1) where ci ∈ C for every i and Σ_{i=1}^{4} |ci|² = 1", and P_{ψ⊗4→ϕ+} = Tr[E1(ψ⊗4)].

Theorem 3 (p. 3): "The success probability of transforming 4 copies of |ψ⟩ into ϕ+ using a universal conclusive ECP based on concatenated two-qubit operations is bounded by P_{ψ⊗4→ϕ+} ⩽ 2|c2⁴c3⁴| + 2|c1⁴c4⁴| − 4Re[c1²c4²(c2*)²(c3*)²]. (8)"

§VIII (p. 6): "For future work, protocols that process four copies directly without intermediate Schmidt-state conversion warrant investigation. We conjecture that such protocols cannot surpass the success probability bound in Eq. (8), although our two-stage approach only rigorously saturates the fundamental limits for concatenated LOCC protocols based on two-qubit operations."

## Reading used by the repository

A pure two-qubit state is its coefficient matrix C = [[c1, c2], [c3, c4]] with Σ|ci|² = 1, and the coefficients of ψ⊗4 pair Alice's four qubits with Bob's. The conjecture is read pointwise: for every universal conclusive LOCC protocol on four copies that processes them directly, and every normalized ψ, Tr E1(ψ⊗4) ≤ B(c), where B(c) is the right-hand side of Eq. (8).
