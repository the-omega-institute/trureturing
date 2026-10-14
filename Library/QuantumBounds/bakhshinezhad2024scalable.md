---
bibkey: bakhshinezhad2024scalable
authors: Pharnam Bakhshinezhad, Mohammad Mehboudi, Carles Roch i Carceller, Armin Tavakoli
year: 2024
title: "Scalable entanglement certification via quantum communication"
doi: 10.1103/PRXQuantum.5.020319
url: https://arxiv.org/abs/2401.00796v2
claim: "In a symmetric prepare-and-measure scenario where Alice and Bob each encode x, y ∈ {0, …, d − 1}² into d-dimensional messages and Charlie, with input z ∈ {0, …, d} and output c, may measure jointly, the average success probability R_d of computing w_z = x₁ + y₁ − 2z(x₀ − y₀) (z ≠ d) and w_d = x₀ − y₀ mod d (Eqs. (27)–(28)) is 1 with shared entanglement; the authors conjecture that without shared entanglement the largest value is R_d = 2/(d + 1) for every odd prime d (Conjecture 1, Eq. (29))."
strata_touched:
  - D5/S3/QuantumBounds/UnentangledOddPrimeCommunication
license: citation-only
triage: anchor
---

# Bakhshinezhad–Mehboudi–Roch i Carceller–Tavakoli, scalable entanglement certification via quantum communication

P. Bakhshinezhad, M. Mehboudi, C. Roch i Carceller and A. Tavakoli, *Scalable entanglement certification via quantum communication*, PRX Quantum **5**, 020319 (2024), DOI 10.1103/PRXQuantum.5.020319; arXiv:2401.00796 [quant-ph] (v2 12 April 2024).

## Verified locator

DOI: 10.1103/PRXQuantum.5.020319 (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2401.00796v2 (the latest of versions v1–v2).
Source: https://arxiv.org/pdf/2401.00796v2 (text read from the PDF):
- §V, Eqs. (18)–(19), the symmetric entanglement-assisted prepare-and-measure scenario and its correlations without shared entanglement;
- §VI, Eqs. (27)–(28), the winning functions and the average success probability, the classical value 2/(d + 1), and Conjecture 1, Eq. (29).

## Source statements

§V, Eq. (19): without shared entanglement, "p(c|x, y, z) = tr(α_x ⊗ β_y M_c|z), where α_x and β_y are d-dimensional states sent from Alice and Bob, respectively, to Charlie. Note that in contrast to the original EAPM scenario, the measurement {M_c|z} can now be entangled." Before Eq. (19): "We remark that all parties can also share classical randomness, which can be included in the state ρ_AB."

§VI: "Let d be an odd prime number. Let Alice and Bob each select one of d² inputs, x = (x₀, x₁) ∈ {0, …, d − 1}² and y = (y₀, y₁) ∈ {0, …, d − 1}². Charlie selects z ∈ {0, …, d} and outputs c ∈ {0, …, d − 1}. The winning conditions correspond to computing the following functions z ≠ d: w_z = x₁ + y₁ − 2z(x₀ − y₀) mod d; z = d: w_d = x₀ − y₀ mod d. (27) The average success probability of computing these functions is R_d = (1/(d⁴(d + 1))) Σ_{x,y,z} p(c = w_z|x, y, z). (28)"

After see-saw searches at d = 3 and d = 5: "Conjecture 1. For every odd prime d, the largest average success probability achievable in a quantum model without shared entanglement is R_d = 2/(d + 1). (29)"

## Reading used by the repository

Inputs are pairs in ZMod d, Charlie's input z ∈ {0, …, d} is `Option (ZMod d)` with `none` for z = d, the messages are d × d density matrices, and Charlie's measurement for each z is a d-outcome POVM on the d²-dimensional joint space. Shared classical randomness is a finite mixture of such strategies with one common index for the three parties. The conjecture is the bound R_d ≤ 2/(d + 1) for every such strategy and mixture, together with its attainment.
