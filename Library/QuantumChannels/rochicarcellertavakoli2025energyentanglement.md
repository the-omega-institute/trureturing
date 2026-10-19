---
bibkey: rochicarcellertavakoli2025energyentanglement
authors: Carles Roch i Carceller; Armin Tavakoli
year: 2025
title: "The role of entanglement in energy-restricted communication and randomness generation"
doi: 10.1088/2058-9565/ae4d80
url: https://arxiv.org/abs/2510.27473v1
claim: "In entanglement-assisted prepare-and-measure scenarios with an energy restriction ⟨0|τ_x^C|0⟩ ≥ 1 − ω on the message, unitary encodings of a shared pure state give no advantage over unassisted quantum communication for the probabilistic transmission of a bit (Result 4); whether unitary encoding remains resourceless for general tasks is left open."
strata_touched:
  - D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
license: citation-only
triage: anchor
---

# Roch i Carceller and Tavakoli, entanglement in energy-restricted communication

C. Roch i Carceller and A. Tavakoli, *The role of entanglement in energy-restricted communication and randomness generation*, arXiv:2510.27473 [quant-ph] (v1 of 31 October 2025), Quantum Sci. Technol. 11, 025020 (2026).

## Verified locator

DOI: https://doi.org/10.1088/2058-9565/ae4d80

Source: https://arxiv.org/abs/2510.27473v1

The text was read from the PDF https://arxiv.org/pdf/2510.27473v1:
- pp. 2–3, §II, Eqs. (1)–(5);
- p. 5, §IV.A and Result 4;
- p. 9, §VI.

## Source statements

pp. 2–3, §II: "This encoding operation corresponds to a completely positive trace-preserving (CPTP) map, Ω_x^{A→C}. The joint state then becomes τ_x^{CB} = (Ω_x^{A→C} ⊗ 1^B)[Ψ^{AB}], (1)" … "p^{QQ}(b|x, y) = Tr[τ_x^{CB} M_{b|y}^{CB}]. (2)" … "⟨0|τ_x^C|0⟩ ≥ 1 − ω, ∀x, (3) where |0⟩_C denotes the vacuum state and where ω is the energy." … "p^{QC}(b|x, y) = Σ_λ q(λ) Tr[ρ_x^{(λ)} M_{b|y}^{(λ)}], (4)" … "The energy constraint in Eq. (3) then simplifies to Σ_λ q(λ)⟨0|ρ_x^{(λ)}|0⟩ ≥ 1 − ω, ∀x. (5)"

p. 5, Result 4: "No protocol that uses unitary encoding operations can provide an entanglement-based advantage in the probabilistic transmission of a bit."

p. 9, §VI: "For quantum communication, we focused on the simplest relevant task and showed that standard unitary encoding operations, commonly used in entanglement-assisted dimension-restricted communication, are resourceless under energy-restrictions. Whether unitary encoding remains resourceless for general tasks is an interesting open problem."

## Reading used by the repository

- A task is a linear figure of merit Σ c(b, x, y) p(b|x, y) over finite inputs, settings and outcomes.
- Unitary encoding is resourceless for a task when, at the same energy ω, every unitary-encoded entanglement-assisted value is matched by some unassisted (QC) value.
- The question is read for ω < 1/2. At ω ≥ 1/2, dense coding with a maximally entangled pair already gives an advantage.
- The companion paper of D'Avino, Senno, Alimuddin and Acín, arXiv:2510.27559, proves the two-input case of resourcelessness for ω < 1/2.
