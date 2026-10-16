---
bibkey: chenklco2026negativityrank
authors: Matthew Chen; Natalie Klco
year: 2026
title: "Susceptibility of qudit-qudit entanglement to quantum noise: insights from the negativity rank"
doi: null
url: https://arxiv.org/abs/2610.10820v1
claim: "For the ordered eigenvalues λ1 ≥ … ≥ λ9 ≥ 0 of a qutrit-qutrit density matrix, ρ is absolutely PPT iff the two 3 × 3 Hildebrand matrices L1, L2 of Eq. (5) are positive semidefinite (Theorem II.1, citing Hildebrand), and L1, L2 have at most one negative eigenvalue (Theorem II.2). §V asks whether this limited rank available for inequality violation persists for the corresponding inequalities in qudit-qudit systems with d > 3."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsolutePPT/HildebrandNegativeIndexRefutation
license: citation-only
triage: anchor
---

# Chen and Klco, negativity rank and qudit-qudit APPT matrices

M. Chen and N. Klco, *Susceptibility of qudit-qudit entanglement to quantum noise: insights from the negativity rank*, arXiv:2610.10820 [quant-ph] (v1 of 7 October 2026, the only version listed).

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2610.10820v1

No DOI or journal reference is listed in the arXiv metadata. The text was read from the PDF https://arxiv.org/pdf/2610.10820v1:
- p. 5, §II C, Theorem II.1 with Eq. (5) and Theorem II.2;
- p. 16, §V (Discussion), the question on d > 3;
- pp. 17–18, Appendix A, the proof of Theorem II.2.

## Source statements

Theorem II.1 (p. 5): "Let λ⃗ be the ordered eigenvalues λ1 ≥ λ2 ≥ · · · ≥ λ9 ≥ 0 of qutrit-qutrit density matrix, ρ. Then, L1 ≡ [[2λ9, λ8 − λ1, λ6 − λ2], [λ8 − λ1, 2λ7, λ5 − λ3], [λ6 − λ2, λ5 − λ3, 2λ4]] ⪰ 0, (5a) L2 ≡ [[2λ9, λ8 − λ1, λ7 − λ2], [λ8 − λ1, 2λ6, λ5 − λ3], [λ7 − λ2, λ5 − λ3, 2λ4]] ⪰ 0 (5b) are both satisfied if and only if ρ is APPT [51]."

Theorem II.2 (p. 5): "If λ⃗ is an ordered vector of qutrit-qutrit density matrix eigenvalues, then L1 and L2 of Eq. (5) have at most one negative eigenvalue."

§V (p. 16): "Unfortunately, the proof provided in Section II C relies on a necessary and sufficient criterion for APPT classification based on linear matrix inequalities [51] that experiences rapid growth in complexity when extended to higher dimensions [51, 66]. Despite this challenge, it may be prudent to explore whether components of the proof, e.g., the limited rank available for inequality violation established in Theorem II.2, persists for the increasing number of corresponding inequalities in qudit-qudit systems with d > 3."

## Reading used by the repository

Reference [51] is Hildebrand, *Positive partial transpose from spectra* (see `hildebrand2007pptspectra`). For a d × d system and a pair of orderings (σ₊, σ₋) in Hildebrand's set Σ±, the corresponding inequality is Λ(σ₊, σ₋) + Λ(σ₊, σ₋)ᵀ ⪰ 0. Its matrix has:
- diagonal entries 2λ_{d²+1−σ₊(k,k)};
- off-diagonal entries λ_{d²+1−σ₊(k,l)} − λ_{σ₋(k,l)} for k < l.

For d = 3 the two elements of Σ± give L1 and L2. The question is read as whether, for every d > 3, every ordered spectrum and every pair in Σ±, this matrix has at most one negative eigenvalue counted with multiplicity. As in Theorem II.2, no APPT condition is imposed on the spectrum.
