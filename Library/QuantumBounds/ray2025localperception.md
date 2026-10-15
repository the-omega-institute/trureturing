---
bibkey: ray2025localperception
authors: Rohit Kishan Ray
year: 2025
title: "Local perception operators and classicality: new tools for old tests"
doi: 10.48550/arXiv.2511.00314
url: https://arxiv.org/abs/2511.00314v1
claim: "For dichotomic observables A_x, B_y with local means a_x = Tr(ρ_A A_x), b_y = Tr(ρ_B B_y) and correlators C_xy = Tr(ρ A_x ⊗ B_y), the symmetric local-perception witness W^s_LPO(ρ) = sup over settings of Σ α_xy a_x b_y C_xy (Eq. (21); for CHSH α = [[1, 1], [1, −1]], Eq. (19)) satisfies W^s_LPO,⊥(ρ) ≤ 2‖r_A‖‖r_B‖ ≤ 2 under mutually orthogonal settings (Theorem 4, Eq. (31)); the author conjectures that for all other measurement settings the upper bound saturates at 2."
strata_touched:
  - D5/S3/QuantumBounds/LocalPerceptionCHSH
license: citation-only
triage: anchor
---

# Ray, local perception operators and classicality

R. K. Ray, *Local perception operators and classicality: new tools for old tests*, arXiv:2511.00314 [quant-ph] (v1 4 November 2025), DOI 10.48550/arXiv.2511.00314.

## Verified locator

DOI: 10.48550/arXiv.2511.00314 (the arXiv DOI; no journal version is listed on the abstract page).
Primary version read: https://arxiv.org/abs/2511.00314v1 (the only arXiv version).
Source: https://arxiv.org/pdf/2511.00314v1 (text read from the PDF):
- §III, Eqs. (4)–(11), the Bell operator, the local perception operators and the local means;
- §III, Eqs. (19) and (21), the CHSH coefficients and the symmetric witness;
- §III, Theorem 4 with Eq. (31), and the conjecture after it;
- §IV, Eqs. (34)–(37), the termwise LPO correlators and the value 2 for |00⟩.

## Source statements

§III: "Consider A_x, B_y to be dichotomic observables with spectra {±1} (POVM, or projective, as required from the context)." Eqs. (10)–(11): "a_x = Tr(ρ_A A_x) ∈ [−1, +1], b_y = Tr(ρ_B B_y) ∈ [−1, +1], along with C_xy = Tr(ρ A_x ⊗ B_y)."

Eq. (21): "W^s_LPO(ρ) := sup_{A_x,B_y} Tr(ρ (B)^A_ρ ⊗ (B)^B_ρ) = sup_{A_x,B_y} [Σ_{x,y} α_xy a_x b_y C_xy + Σ_x β_x a_x² + Σ_y γ_y b_y²]."

Eq. (35): "C^LPO_ij = Tr(ρ (X_ij)^A_ρ ⊗ (X_ij)^B_ρ) = a_i b_j C_ij."

After Eq. (31): "Therefore, we see under mutually orthogonal setting condition, the upper bound is tighter and it is 2. In fact, we will now see, that for pure states and other various states, this bound remains the numerically achievable bound. Therefore, we conjecture that for all other conceivable measurement settings, the upper-bound of W^s_LPO(ρ) saturates at 2."

§V: "Our numerical results further suggest a CHSH-type upper-bound of 2 for the optimized symmetric case, which we state as a conjecture."

## Reading used by the repository

The repository takes W^s_LPO as the termwise sum of Eq. (21), second line, which is Σ α_ij C^LPO_ij of Eq. (35) and the quantity of Eq. (37). The first line of Eq. (21) is a different functional: for |00⟩ with σ_z everywhere it equals 4, while the termwise sum equals 2.
