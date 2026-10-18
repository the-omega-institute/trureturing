---
bibkey: zuppardo2019entanglementgain
authors: Margherita Zuppardo; Ray Ganardi; Marek Miller; Somshubhro Bandyopadhyay; Tomasz Paterek
year: 2019
title: "Entanglement gain in measurements with unknown results"
doi: 10.1103/PhysRevA.99.042319
url: https://arxiv.org/abs/1806.05465v1
claim: "A non-selective measurement in an orthonormal basis {|ψ_j⟩} maps a pure state |φ⟩ to ρ′ = Σ_j |⟨ψ_j|φ⟩|² |ψ_j⟩⟨ψ_j|; for two qubits and the measurement bases (28), the largest final negativity satisfies N^max_f − N_i = 1/4 − N_i/2 (Eq. (33)), and the authors leave open whether this is optimal among all measurement bases."
strata_touched:
  - D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum
license: citation-only
triage: anchor
---

# Zuppardo, Ganardi, Miller, Bandyopadhyay and Paterek, entanglement gain in measurements with unknown results

M. Zuppardo, R. Ganardi, M. Miller, S. Bandyopadhyay and T. Paterek, *Entanglement gain in measurements with unknown results*, Phys. Rev. A 99, 042319 (2019), DOI 10.1103/PhysRevA.99.042319; arXiv:1806.05465 [quant-ph] (v1, 14 June 2018, the only version).

## Verified locator

DOI: 10.1103/PhysRevA.99.042319

Source: https://arxiv.org/abs/1806.05465v1; the text was read from the PDF.
- page 3: Theorems 2 and 3 with the post-measurement state;
- pages 4–5: Section I.E, Eqs. (28)–(33), and the open optimality question.

## Source statements

Theorem 2: "ρ′ = Σ_{j=0}^{D−1} |⟨ψ_j|φ⟩|² |ψ_j⟩⟨ψ_j|".

Eq. (33): "N^max_f − N_i = 1/4 − N_i/2".

Section I.E: "Finally, we address the issue whether results just presented are globally optimal. In order to derive them we assumed the measurement basis of the form (28). Although we were not able to provide a proof that this is indeed the optimal choice among all possible measurement bases, we have conducted numerical check which supports optimality."

## Reading used by the repository

**Definitions.**
- For a unit two-qubit vector ψ and a unitary U, the measured state is Σ_j (U†ψψ†U)_jj u_j u_j†, where u_j are the columns of U.
- The negativity is that of the source, with the partial transpose on the second qubit.

**The theorem.** The repository proves that the negativity of the measured state is at most N(ψψ†)/2 + 1/4 for every U, with equality for some U. This is the global optimality of Eq. (33).
