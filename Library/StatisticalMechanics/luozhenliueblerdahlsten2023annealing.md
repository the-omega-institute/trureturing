---
bibkey: luozhenliueblerdahlsten2023annealing
authors: Yutong Luo; Yi-Zheng Zhen; Xiangjing Liu; Daniel Ebler; Oscar Dahlsten
year: 2023
title: "Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing"
doi: 10.1103/PhysRevE.108.054119
url: https://arxiv.org/abs/2311.10424v1
claim: "For simulated annealing with Glauber acceptance, P_ij = γ_i/(|N(j)|(γ_i + γ_j)) on neighbours (Eqs. (30)–(32)), the relaxation rate is µ = (E′_p − E_p)/(E′_γ − E_p) (Eq. (46)), and a partial swap model p′ = p + µ^PS(γ′ − p) has λ_2(P′^PS) = 1 − µ^PS (Eq. (43), Proposition 2). With τ_rel(P) = 1/(1 − λ_2(P)), the authors conjecture that τ_rel ≤ τ^PS_rel implies µ ≥ µ^PS (Eq. (50))."
strata_touched:
  - D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation
license: citation-only
triage: anchor
---

# Luo, Zhen, Liu, Ebler and Dahlsten, bound on annealing performance from stochastic thermodynamics

Y. Luo, Y.-Z. Zhen, X. Liu, D. Ebler and O. Dahlsten, *Bound on annealing performance from stochastic thermodynamics, with application to simulated annealing*, Phys. Rev. E **108**, 054119 (2023), DOI 10.1103/PhysRevE.108.054119; arXiv:2311.10424 [cond-mat.stat-mech] (v1, the only version).

## Verified locator

DOI: 10.1103/PhysRevE.108.054119 (as listed in the arXiv metadata, with journal reference Phys. Rev. E 108, 054119 (2023)).
Primary version read: https://arxiv.org/abs/2311.10424v1.
Source: https://arxiv.org/pdf/2311.10424v1 (text read from the PDF):
- §IV.A, Eqs. (30)–(32): the SA chain and the Glauber acceptance rate;
- §IV.C, Eqs. (42)–(46): the partial swap model, µ^PS and µ;
- page 8, Eq. (50) and Proposition 2.

The journal version was not read.

## Source statements

§IV.A: "p_i(k + 1) = Σ_j P_ij(k + 1) p_j(k), (30)", with P_ij(k) = A_ij(k)/|N(j)| for i ∈ N(j), P_jj(k) = 1 − Σ_{l≠j} P_lj(k), and 0 otherwise (31), and the Glauber rate "A_ij(k) = 1/(1 + exp(β(k)ΔE_ij)) = γ_i(k)/(γ_i(k) + γ_j(k)), (32)".

§IV.C: "p′^PS_i = p^PS_i + µ^PS(γ′^PS_i − p^PS_i), (43)" and "Similarly, we can define a relaxation rate µ for the actual process in SA as µ := (E′_p − E_p)/(E′_γ − E_p). (46) … Since in SA, E_p ≥ E_γ ≥ E′_γ, we need the assumption that E_p ≥ E′_p."

Page 8: "The relaxation time τ_rel(P) ≡ 1/(1 − λ_2(P)) of the discrete Markov chain [31], defined by the second largest eigenvalue of the transition matrix P, λ_2(P), should be consistent with µ. Therefore, we conjecture that the order of relaxation times of the two processes corresponding to µ and µ^PS is the inverse order of µ and µ^PS, i. e. τ_rel ≤ τ^PS_rel ⇒ µ ≥ µ^PS. (50)"

Proposition 2: "For a partial swap model given by Eq. (43), λ_2(P′^PS) = 1 − µ^PS."

## Reading used by the repository

The state space is finite, with a symmetric, irreflexive neighbourhood in which every state has n ≥ 1 neighbours. Inverse temperatures are positive and strictly increasing along the schedule. The chain starts in the Gibbs state at β(0). At a step k with E_p ≥ E′_p, E_p ≥ E_γ ≥ E′_γ and E′_γ ≠ E_p, and for a partial swap rate 0 < m ≤ 1, the conjecture is read as: m ≤ 1 − λ_2(P(β(k + 1))) implies µ(k) ≥ m. Here λ_2 is the second largest eigenvalue counted with multiplicity. The gap form m ≤ 1 − λ_2 restates τ_rel ≤ τ^PS_rel = 1/m (Proposition 2) and excludes λ_2 = 1.
