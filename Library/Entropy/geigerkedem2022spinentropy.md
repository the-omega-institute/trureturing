---
bibkey: geigerkedem2022spinentropy
authors: Davi Geiger; Zvi M. Kedem
year: 2022
title: "Spin Entropy"
doi: 10.3390/e24091292
url: https://arxiv.org/abs/2111.11605v3
claim: "The spin-entropy of a pure spin state is the Shannon entropy of the S_z probabilities plus the differential entropy of the polarization-angle density ρ_s(φ) = |λ_s(φ)|² (Eq. (4)). For spin 1, with the state (15) and the density ρ_1 of Proposition 2, the authors conjecture (Conjecture 1) that the spin-entropy depends only on the variables θ_α, θ_β of the z-axis component, so that Eq. (17) simplifies to its zero-phase form Eq. (18)."
strata_touched:
  - D5/S3/Entropy/GeigerKedemSpinEntropyPhaseRefutation
license: citation-only
triage: anchor
---

# Geiger–Kedem, spin entropy

D. Geiger and Z. M. Kedem, *Spin Entropy*, Entropy **24**, 1292 (2022), DOI 10.3390/e24091292; arXiv:2111.11605 [quant-ph] (v3, the latest of versions v1–v3).

## Verified locator

DOI: 10.3390/e24091292 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2111.11605v3.
Source: https://arxiv.org/pdf/2111.11605v3 (text read from the PDF):
- §II, Eqs. (1)–(4), the phase-space wave function and the spin-entropy;
- §III, Spin 1, Eq. (15), Proposition 2 with Eq. (17), and Conjecture 1 with Eq. (18), pages 19–21.

## Source statements

Eq. (15): "|ξ_z⟩ = e^{iφ_y}(sin θ_α cos θ_β e^{iφ_x}|↑⟩_z + cos θ_α |→⟩_z + sin θ_α sin θ_β e^{iφ_z}|↓⟩_z), with θ_α, θ_β ∈ [0, π/2], and φ_x, φ_z, φ_y ∈ [0, 2π)."

Proposition 2: "The spin-entropy of a particle with spin s = 1 in a state given by (15) is S_1 = −∫_0^{2π} ρ_1(φ, φ_x, φ_z, θ_α, θ_β) ln ρ_1(φ, φ_x, φ_z, θ_α, θ_β) dφ + S_c(cos²θ_α) + sin²θ_α S_c(cos²θ_β), (17) where S_c(cos²θ) = −cos²θ ln(cos²θ) − (1 − cos²θ) ln(1 − cos²θ), ρ_1(φ) = (1/2π)|sin θ_α cos θ_β e^{i(φ_x+2φ)} + cos θ_α e^{iφ} + sin θ_α sin θ_β e^{i(φ_z−2φ)}|²."

Page 20: "Observed in simulations and in (14), we conjecture that Conjecture 1. The spin-entropy depends only on the variables that define the spin-entropy component along the z axis. In particular, the spin-entropy (17) of a state given by (15) can be simplified to S_1(θ_α, θ_β) = −∫_0^{2π} ρ(φ, θ_α, θ_β) ln ρ(φ, θ_α, θ_β) dφ + S_c(cos²θ_α) + sin²θ_α S_c(cos²θ_β), (18) where ρ(φ, θ_α, θ_β) = (1/2π)|sin θ_α cos θ_β e^{i2φ} + cos θ_α e^{iφ} + sin θ_α sin θ_β e^{−i2φ}|²."

## Reading used by the repository

The conjecture is read as: for all θ_α, θ_β ∈ [0, π/2] and φ_x, φ_z ∈ [0, 2π), the value of Eq. (17) equals its value at φ_x = φ_z = 0. The global phase φ_y does not enter ρ_1. The integral is the interval integral over [0, 2π] of the continuous function φ ↦ ρ_1 ln ρ_1.

The authors' later paper, D. Geiger, *Phase Space Spin-Entropy*, Entropy 26, 372 (2024), DOI 10.3390/e26050372, replaces this phase-space decomposition by an entropy on the sphere.
