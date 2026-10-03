---
bibkey: serranoensastiga2026monogamy
authors: Eduardo Serrano-Ensástiga; Olivier Giraud; John Martin
year: 2026
title: "Multiqubit monogamy relations beyond shadow inequalities"
doi: 10.1103/9fkf-hm8l
url: https://arxiv.org/abs/2507.12680v2
claim: "For a bipartition A|Abar of an N-qubit system into k = |A| and N - k qubits, with rho_A the reduced state of a pure state, rho~ = sigma_y^(tensor k) rho* sigma_y^(tensor k) and R_rho = Tr(rho rho~), the authors conjecture that the minimum of Tr(rho_A^2) + R_(rho_A) over pure states is 2^(k-N) if 2k > N and 2^(1-k) if 2k <= N (Conjecture 2; proved there for k = 1, numerical for 2k <= N, k >= 2)."
strata_touched:
  - D5/S3/Quantum/Entanglement/PurityTimeReversalOverlapMinimum
license: citation-only
triage: anchor
---

# Multiqubit monogamy relations beyond shadow inequalities

E. Serrano-Ensástiga, O. Giraud and J. Martin, arXiv:2507.12680 (v2
2026-01-07); Phys. Rev. A 113 (2026) 012415. Subject: quant-ph.

The paper derives inequalities between the sector lengths `S_m` of multiqubit
states. One family comes from the time-reversed state
`ρ̃ = σ_y^{⊗N} ρ^* σ_y^{⊗N}` and the overlap `R_ρ = Tr(ρ ρ̃)`, evaluated on the
reduced state `ρ_A` of a pure state across a bipartition `A | Ā` with
`|A| = k`. Proposition 1 gives
`2^{−min(k, N−k)} ≤ Tr(ρ_A²) + R_{ρ_A} ≤ (3 + (−1)^k)/2`. The section on the
overlap `R_ρ` proves that the sum is `1` for `k = 1`, reports numerical minima
for `N ≤ 10`, and states:

> Let $A|\bar{A}$ be a bipartition of an $N$-qubit system into $k=|A|$ and
> $N-k=|\bar{A}|$ qubits. Then, the minimum of
> $\mathrm{Tr}(\rho_A^2) + R_{\rho_A}$ taken over all pure states
> $|\psi\rangle$ of the $N$-qubit system, is given by
> $\min_{|\psi\rangle} \big(\mathrm{Tr}(\rho_A^2) + R_{\rho_A}\big) =
> 2^{k-N}$ if $2k > N$, and $2^{-k + 1}$ if $2k \leq N$.

## Verified locator

- DOI: https://doi.org/10.1103/9fkf-hm8l (Crossref record; the journal text
  was not read).
- URL: https://arxiv.org/abs/2507.12680v2 (source `arXiv_v2.tex` retrieved
  2026-10-01): the definitions of the time-reversed state and of `R_ρ`
  (Sec. II), Proposition 1 (Sec. III), and Conjecture 2 at the end of
  Sec. V, in its subsection "The overlap `R_ρ`".
