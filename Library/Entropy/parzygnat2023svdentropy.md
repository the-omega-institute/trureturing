---
bibkey: parzygnat2023svdentropy
authors: Arthur J. Parzygnat, Tadashi Takayanagi, Yusuke Taki, Zixia Wei
year: 2023
title: "SVD entanglement entropy"
doi: 10.1007/JHEP12(2023)123
url: https://arxiv.org/abs/2307.06531v2
claim: "For two states the SVD entanglement entropy is the von Neumann entropy of the normalized absolute value √(τ†τ)/Tr √(τ†τ) of the reduced transition matrix τ = Tr_B|ψ¹⟩⟨ψ²|/⟨ψ²|ψ¹⟩; it lies between 0 and log d_A. The authors give numerical evidence that the lower bound min{S(ρ¹_A), S(ρ²_A)} might hold for qubits (failing for qudits), state that rigorous proofs for qubits are lacking, and prove it only when the second state is a local unitary image of the first (Eq. (3.37)), a restricted version of Eq. (3.38)."
strata_touched:
  - D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound
license: citation-only
triage: anchor
---

# Parzygnat–Takayanagi–Taki–Wei, SVD entanglement entropy

A. J. Parzygnat, T. Takayanagi, Y. Taki and Z. Wei, *SVD entanglement entropy*, JHEP **12** (2023) 123, DOI 10.1007/JHEP12(2023)123; arXiv:2307.06531 [hep-th] (v2, the latest of versions v1–v2).

## Verified locator

DOI: 10.1007/JHEP12(2023)123 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2307.06531v2.
Source: https://arxiv.org/pdf/2307.06531v2 (text read from the PDF):
- §2, the reduced transition matrix, the SVD density matrix and the SVD entanglement entropy;
- §3.3, the bounds 0 ≤ S ≤ log d_A, Figure 8 and the conjectured qubit lower bound;
- §3.4, Eqs. (3.29)–(3.38), the local-unitary case and the general inequality (3.38).

## Source statements

§3.3: "In the examples of Section 3.2, we explored the possibilities of improving this upper bound of log(d_A) and possibly finding an improved lower bound in terms of the minimum of the marginal SVD entropies. In Figure 8, we provide numerical evidence suggesting that a non-trivial lower bound of min{S(ρ¹_A), S(ρ²_A)} might hold for qubits, fails in general for qudits, but seems to have a higher probability of holding as d_A increases. Rigorous proofs of these observations for qubits and asymptotically large systems, provided that they hold, are still lacking."

§3.4, after Eq. (3.37), which is proved for |ψ₂⟩ = (U ⊗ I)|ψ₁⟩: "Note that the conclusion here is a restricted version of S(ρ^{1|2}_B) ?≥ min{S(ρ¹_B), S(ρ²_B)}, (3.38) to the cases where S(ρ¹_B) = S(ρ²_B)."

## Reading used by the repository

A two-qubit pure state is its coefficient matrix A (ψ = Σ A_{ij}|ij⟩) with Frobenius norm 1. The reduced transition is Tr_B|ψ⟩⟨φ| = A B†; the factor 1/⟨φ|ψ⟩ cancels in the SVD density matrix, so the statement covers every pair with nonzero reduced transition. Entropies are Σ −λ log λ over eigenvalues (natural logarithm).
