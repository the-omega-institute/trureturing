---
bibkey: basso2020correlatedcoherence
authors: Marcos L. W. Basso; Jonas Maziero
year: 2020
title: "Monogamy and trade-off relations for correlated quantum coherence"
doi: 10.1088/1402-4896/abafcb
url: https://arxiv.org/abs/2006.14037v2
claim: "For the l1-norm coherence C in a fixed product basis, the correlated coherence of a bipartite marginal is C(ρ_XY) − C(ρ_X) − C(ρ_Y), and C^c(ρ_A|BC) − C^c(ρ_AB) − C^c(ρ_AC) = C(ρ_ABC) + Σ_α C(ρ_α) − Σ_{α<β} C(ρ_αβ) (Eq. (33)); the paper proves the monogamy relation under conditions (22)–(24) and conjectures that it holds for every tripartite pure state."
strata_touched:
  - D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation
license: citation-only
triage: anchor
---

# Basso and Maziero, monogamy of correlated quantum coherence

M. L. W. Basso and J. Maziero, *Monogamy and trade-off relations for correlated quantum coherence*, Phys. Scr. 95, 095105 (2020), DOI 10.1088/1402-4896/abafcb; arXiv:2006.14037 [quant-ph] (v2, 3 September 2020).

## Verified locator

DOI: 10.1088/1402-4896/abafcb

Source: https://arxiv.org/abs/2006.14037v2; the text was read from the PDF.
- page 1: the introduction and the conjecture;
- pages 3–5: the l1-norm coherence and the correlated coherence, Theorem 3, Eqs. (22)–(30);
- page 5: Theorem 4, Eqs. (31)–(35);
- pages 6–7: Section III.A, Eqs. (36)–(42), and the conjecture.

## Source statements

Introduction: "we conjecture that is monogamous, at least, for tripartite pure quantum states".

Theorem 4: "C^c(ρ_A|BC) := C^c(ρ_ABC) − C(ρ_A) − C(ρ_BC) denotes the correlated coherence between A and BC".

Eq. (33): "C^c(ρ_A|BC) − C^c(ρ_AB) − C^c(ρ_AC) = C(ρ_ABC) + Σ_{α=A,B,C} C(ρ_α) − Σ_{α<β=A,B,C} C(ρ_αβ)".

Section III.A: "Therefore, the conditions expressed by the equations (22), (23), and (24) are sufficient but not necessary, and seems reasonably to conjecture that the monogamy relation C^c_l1(ρ_A|BC) ≥ C^c_l1(ρ_AB) + C^c_l1(ρ_AC) holds for any tripartite pure quantum state."

## Reading used by the repository

**The quantity.** For a unit vector on three qubits, the repository takes:
- the l1 coherence C(ρ) = Σ_{i≠j} |ρ_ij| of each reduced state in the computational product basis;
- M = C(ρ_ABC) + C(ρ_A) + C(ρ_B) + C(ρ_C) − C(ρ_AB) − C(ρ_AC) − C(ρ_BC), which by Eq. (33) equals C^c(ρ_A|BC) − C^c(ρ_AB) − C^c(ρ_AC).

**The refutation.** It refutes 0 ≤ M for three qubits, which refutes the conjecture. The witness is the normalized vector (−16, 1, 128, −16, −128, −16, 1, −128)/√49922 in the order |000⟩, …, |111⟩, with M = −383/24961.
