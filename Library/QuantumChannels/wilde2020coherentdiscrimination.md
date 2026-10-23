---
bibkey: wilde2020coherentdiscrimination
authors: Mark M. Wilde
year: 2020
title: "Coherent Quantum Channel Discrimination"
doi: 10.1109/ISIT44484.2020.9174425
url: https://arxiv.org/abs/2001.02668v1
claim: "In coherent channel discrimination the prover's success probability p^coh_s(N⁰, N¹) is the supremum over pure inputs and prover unitaries of Eq. (17), independent of the isometric extensions; it satisfies 1/2 ≤ p^coh_s ≤ 1 (Proposition 2), and Section VI asks whether p^coh_s − 1/2 is a metric on quantum channels."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/CoherentDiscriminationTriangleRefutation
license: citation-only
triage: anchor
---

# Wilde, coherent quantum channel discrimination

M. M. Wilde, *Coherent Quantum Channel Discrimination*, in Proceedings of the 2020 IEEE International Symposium on Information Theory (ISIT), DOI 10.1109/ISIT44484.2020.9174425; arXiv:2001.02668 [quant-ph] (v1 8 January 2020, the only version).

## Verified locator

DOI: 10.1109/ISIT44484.2020.9174425

Source: https://arxiv.org/abs/2001.02668v1; the text was read from the PDF.
- pages 3–4: Section II, the isometric extensions (10) and the coherent game, Eqs. (11)–(18);
- page 4: Propositions 1 and 2;
- page 5: Section VI, the open question.

## Source statements

Eq. (17): "p^coh_s(N⁰, N¹, |ψ⟩_RA, V_RBE′F) := (1/2) ‖⟨Φ|_R1F ⟨0|_G Σ_{i∈{0,1}} |i⟩_R1 W^{i†} V W^i |ψ⟩_RA |000⟩_GE′F‖²₂ = (1/2) ‖⟨Φ|_R1F Σ_{i∈{0,1}} |i⟩_R1 U^{i†} V U^i |ψ⟩_RA |00⟩_E′F‖²₂".

After Eq. (17): "the success probability in (17) is independent of the particular isometric extension U^i of the original channel N^i_{A→B} for both i = 0 and i = 1."

Eq. (18): "p^coh_s(N⁰, N¹) := sup_{|ψ⟩,V} p^coh_s(N⁰, N¹, |ψ⟩_RA, V_RBE′F)."

Proposition 2: "1/2 ≤ p^coh_s(N⁰, N¹) ≤ 1."

Section VI: "An intriguing open question is to determine if p^coh_s − 1/2 is a metric on quantum channels. Consider that p^inc_s − 1/2 is, as is clear from (8)."

## Reading used by the repository

For qubit channels given by Kraus families with four operators, the repository uses the canonical isometric extension U|φ⟩ = Σ_k K_k|φ⟩ ⊗ |k⟩_E and takes the supremum of Eq. (17) over all finite reference systems, unit inputs, finite ancillas and prover unitaries. The value does not depend on the isometric extension (after Eq. (17)), so a metric property of p^coh_s − 1/2 on channels implies the triangle inequality on these Kraus families; the repository refutes that triangle inequality.
