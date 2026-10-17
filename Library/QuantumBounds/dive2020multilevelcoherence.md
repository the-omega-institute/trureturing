---
bibkey: dive2020multilevelcoherence
authors: Benjamin Dive; Nikolaos Koukoulekidis; Stefanos Mousafeiris; Florian Mintert
year: 2020
title: "Characterisation of multi-level quantum coherence without ideal measurements"
doi: 10.1103/PhysRevResearch.2.013220
url: https://arxiv.org/abs/1901.08599v3
claim: "For the interference pattern p(t) = ⟨χ|e^{−iHt} ρ e^{iHt}|χ⟩ of a commensurate Hamiltonian, the moment ratio R3 = M3/M1² is convex in ρ and its maximum over states that are not (k + 1)-coherent is a threshold for k-coherence; Table I gives the values 1 (k = 1), 5/4 (k = 2) and, for k = 3, only the analytic upper bound 179/96 and the numerical value 1.77."
strata_touched:
  - D5/S3/Quantum/Measurement/ThreeCoherenceRamseyThreshold
license: citation-only
triage: anchor
---

# Dive, Koukoulekidis, Mousafeiris and Mintert, multi-level coherence without ideal measurements

B. Dive, N. Koukoulekidis, S. Mousafeiris and F. Mintert, *Characterisation of multi-level quantum coherence without ideal measurements*, Phys. Rev. Research 2, 013220 (2020), DOI 10.1103/PhysRevResearch.2.013220; arXiv:1901.08599 [quant-ph] (v3, 27 February 2020; the published version).

## Verified locator

DOI: 10.1103/PhysRevResearch.2.013220

Source: https://arxiv.org/abs/1901.08599v3. The text was read from the PDF.
- Page 1: the definition of k-coherence.
- Page 2: the Hamiltonians (1), the moments (2) and the ratios (3).
- Page 3: Table I and Eqs. (4)–(7).

## Source statements

Page 1: "one can define pure states |ψ⟩ = Σ_j ψ_j |j⟩ with at least k non-vanishing amplitudes ψ_j to be k-coherent. Extending this, a mixed state ρ is k-coherent if all decompositions ρ = Σ_i p_i |ψ_i⟩⟨ψ_i| into pure states |ψ_i⟩ with p_i ≥ 0 contains at least one k-coherent pure state".

Page 2: "We make no restrictions on this Hamiltonian other than it being time-independent and having a discrete and commensurate spectrum … there is no loss of generality in only considering Hamiltonians H = Σ_n n|n⟩⟨n| (1)".

Eq. (2): "M_n(ρ, |χ⟩) = (1/2π)∫₀^{2π} p(t)^n dt = (1/2π)∫₀^{2π} ⟨χ|e^{−iHt} ρ e^{iHt}|χ⟩^n dt".

Eq. (3): "R_n(ρ, |χ⟩) = M_n/M_1^{n−1}".

Page 2: "In the cases where the exact threshold values are not known, we use numerical methods to approximate them".

Table I: "k-coherence | R3 Threshold | R3 Best Known: 1 | 1 | 1; 2 | 5/4 | 1.25; 3 | 179/96 ≈ 1.86 | 1.77. TABLE I. The maximum values that R3(ρ, |χ⟩) can attain, under any Hamiltonian, for any |χ⟩ and for any ρ ∈ C_k as a function of k. As such, exceeding these values means that the state must be at least (k + 1)-coherent. The middle column is an upper bound to this highest value obtained analytically. The last column is the highest value we found after conducting a thorough numerical optimisation."

## Reading used by the repository

In Table I, C_k denotes the states that are not (k + 1)-coherent, which by the page-1 definition are the finite mixtures of pure states with at most k nonzero amplitudes. Table I's second sentence and the value 1 at k = 1 fix this reading.

The repository takes:
- the Hamiltonian H = diag(n_j) with integer labels, which contains the source's form (1);
- unit measurement vectors χ;
- R3 over every finite dimension, over the mixtures of unit vectors with at most three nonzero amplitudes, and over the inputs with M1 > 0.

It proves that the maximum of R3 in the row k = 3 is N(α)/D(α) ≈ 1.7731757563, where:
- N(r) = r⁶ + 30r⁴ + 90r² + 20;
- D(r) = (r + 2)²(r² + 2)²;
- α is the root of r⁷ − 13r⁶ + 6r⁵ − 60r⁴ + 30r³ − 30r² + 140r − 20 in (6169/5000, 12339/10000).

The maximum is attained at the energies 0, 1, 2 by ψ = χ with the populations (1, α, 1)/(α + 2).
