---
bibkey: gu2024crosscorrelationactivity
authors: Jie Gu
year: 2024
title: "Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production"
doi: 10.1103/PhysRevE.109.L042101
url: https://arxiv.org/abs/2312.00354v2
claim: "For a Markov jump process on N states, the normalized asymmetry of cross-correlation obeys |χ_ab| ≤ γ/tan(π/N) · √(σ/(2A)) (Eq. (8)), proved for unicyclic networks; the author conjectures Eq. (8) for arbitrary networks and proves the weaker Eq. (9) in general."
strata_touched:
  - D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation
license: citation-only
triage: anchor
---

# Gu, thermodynamic bounds on the asymmetry of cross-correlations

J. Gu, *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*, Phys. Rev. E **109**, L042101 (2024), DOI 10.1103/PhysRevE.109.L042101; arXiv:2312.00354 [cond-mat.stat-mech] (v1 1 December 2023; v2 5 April 2024).

## Verified locator

DOI: 10.1103/PhysRevE.109.L042101 (Crossref: Physical Review E 109, article L042101, published 4 April 2024).
Primary version read: https://arxiv.org/abs/2312.00354v2; the text was read from the PDF.
- pp. 1–2, "Setup": Eqs. (1)–(7);
- p. 2, "Main result": Eqs. (8)–(9) and the conjecture after them, with Fig. 1(d).

The journal typesetting was not compared line by line.

## Source statements

Setup: "Consider a stochastic Markov jump process with finite N states. … W_mn (m ≠ n) is the time-independent transition rate from state n to m, and the rate of leaving state m is W_mm = −Σ_{n(≠m)} W_nm. Thermodynamic consistency is assumed, i.e., whenever W_mn ≠ 0, W_nm is nonzero too. … the system is in a nonequilibrium steady state p^ss satisfying W p^ss = 0. After defining the one-way flux T_mn = W_mn p^ss_n … γ ≡ max T_mn / min T_mn, for T_mn > 0. (3) … A = Σ_{m≠n} T_mn = Σ_{m>n} A_mn, σ = Σ_{m≠n} T_mn ln(T_mn/T_nm). (4)"

Eqs. (6)–(7): "χ_ab ≡ α_ab/√(D_a D_b)", "α_ab = (1/2) Σ_{m,n} (a_n b_m − a_m b_n) T_mn = Σ_{m<n} Ω_mn J_mn, (D_a + D_b)/2 = (1/4) Σ_{m,n} [(a_m − a_n)² + (b_m − b_n)²] T_mn".

Main result: "|χ_ab| ≤ γ/tan(π/N) · √(σ/(2A)) (8) and |χ_ab| ≤ √(N*γ/(2π tan(π/N))) · √(σ/A), (9) where N* is the number of nonzero local activities. The derivation of Eq. (8) for unicyclic networks and Eq. (9) for general cases is deferred to the end of the Letter. We conjecture that Eq. (8) is valid for arbitrary networks, and present numerical evidence in Fig. 1(d), with a total of 10⁶ data points and three distinct topologies".

## Reading used by the repository

The sum in σ ranges over pairs with positive one-way flux, which by the bidirectional support also have positive reverse flux. D_a = (1/2) Σ_{m,n} (a_m − a_n)² T_mn, the auto-correlation slope implied by Eq. (7). The conjecture is read for every N ≥ 3, every bidirectional network with a stationary probability, at least one positive flux, and observables with D_a D_b > 0.
