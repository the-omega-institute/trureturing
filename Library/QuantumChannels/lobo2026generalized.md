---
bibkey: lobo2026generalized
authors: E. P. Lobo; M. Balanzó-Juandó; S. Pironio
year: 2026
title: "Generalized measurement incompatibility"
doi: 10.48550/arXiv.2605.16151
url: https://arxiv.org/abs/2605.16151v1
claim: "Measurements are G-jointly measurable when a common parent reproduces them while determining only the outcomes in the subsets G_y; for two lossy projective qubit measurements whose axes are separated by an angle θ ∈ [0, π/2], with G = ({+,−}, ∅), the paper proves G-joint measurability for η ≤ 2/(2 + sin θ) and reports that this bound is tight up to machine precision."
strata_touched:
  - D5/S3/Quantum/Measurement/LossyQubitPartialJMTightness
license: citation-only
triage: anchor
---

# Lobo, Balanzó-Juandó and Pironio, generalized measurement incompatibility

E. P. Lobo, M. Balanzó-Juandó and S. Pironio, *Generalized measurement incompatibility*,
arXiv:2605.16151v1 (15 May 2026; quant-ph).

## Verified locator

DOI: 10.48550/arXiv.2605.16151.
Primary version read: https://arxiv.org/abs/2605.16151v1 (the only version).
Source: https://arxiv.org/pdf/2605.16151v1 (text read from the PDF):
- §II.C, Definition 2 (p. 3);
- §IV, Eq. (13) (p. 4);
- §IV.B, Eqs. (18)–(19) and case (d) with Eq. (36) (p. 8).

## Source statements

Definition 2: "Given a collection of subsets G = (G_y)_y with G_y ⊆ [k_y], the measurements B_y = {B_{b|y}}_b are said to be G-jointly measurable if there exist POVM elements E_{β̄,b|y} such that Σ_b E_{β̄,b|y} = E_β̄ ∀y ∈ [n] (no-signaling), (9) B_{b|y} = Σ_β̄ E_{β̄,b|y} (consistency), (10) E_{β̄,b|y} = δ_{b,β_y} E_{β̄,⋆|y} ∀b ∈ G_y (partial JM), (11) for some positive operator E_{β̄,⋆|y} := E_β̄ − Σ_{b∈Ḡ_y} E_{β̄,b|y} independent of b." The bar over G_y denotes the complement of G_y in the outcome set (checked against the rendered PDF, p. 3).

Eq. (13): "the POVM elements of an ideal measurement B_y = {B_{b|y}}_b are modified as B^η_{b|y} = ηB_{b|y} if b ≠ ∅, (1 − η)𝟙 if b = ∅".

Eqs. (18)–(19): "B_y = r_y · σ, y ∈ {1, …, n}, where r_y ∈ ℝ³ are unit Bloch vectors, ‖r_y‖ = 1 … The corresponding POVM elements are the rank-one projectors B_{±|y} = ½(𝟙 ± r_y · σ) =: P_{±r_y}".

Case (d), p. 8: "In the case of n = 2 measurements separated by an angle θ ∈ [0, π/2] on the Bloch sphere, we find that the bound can be improved to η ≤ 2/(2 + sin(θ)). (36) … We find numerically by solving the G-JM SDP for a large number of values of θ ∈ [0, π/2] that, up to machine precision, this bound is tight."
