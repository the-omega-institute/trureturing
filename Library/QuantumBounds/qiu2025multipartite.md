---
bibkey: qiu2025multipartite
authors: Xinyu Qiu; Zhiwei Song; Lin Chen
year: 2025
title: "Multipartite entangling power by von Neumann entropy"
doi: 10.1103/PhysRevA.111.022407
url: https://arxiv.org/abs/2410.15253v1
claim: "The entanglement generation K_{L:L^c}(U) of an n-partite unitary U is the supremum, over pure inputs psi_i of each party A_i with a local auxiliary system R_i, of the von Neumann entropy in ebits of the reduced state on L of U(psi_1 ⊗ ... ⊗ psi_n); for the four-qubit Fredkin gate F_4 the paper shows K_{AD:BC}(F_4) ∈ [2, log_2 5] and conjectures K_{AD:BC}(F_4) = 2."
strata_touched:
  - D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation
license: citation-only
triage: anchor
---

# Multipartite entangling power by von Neumann entropy

X. Qiu, Z. Song and L. Chen, arXiv:2410.15253 (v1 2024-10-20, the only arXiv
version); Phys. Rev. A 111, 022407 (2025). Subject: quant-ph.

The paper defines the entangling power of an `n`-partite unitary
`U_{A_1,…,A_n}` as the supremum, over pure inputs `ψ_i ∈ H_{A_iR_i}` with
local auxiliary systems `R_i`, of the largest von Neumann entropy across a
bipartition `L : L^c` of `U(ψ_1 ⊗ ⋯ ⊗ ψ_n)` (Definition `def:N-ep`); for a
fixed `L` the inner supremum is `K_{L:L^c}(U)`. For the four-qubit Fredkin gate

`F_4 = (|00⟩⟨00| + |01⟩⟨01| + |10⟩⟨10|)_{AB} ⊗ (I_2^{⊗2})_{CD} + |11⟩⟨11|_{AB} ⊗ (S_2)_{CD}`

the paper computes `K` for the cuts `A:BCD`, `C:ABD` and `AB:CD`. For `AD:BC`
it bounds `K_{AD:BC}(F_4)` below by 2, using the input
`|10⟩|10⟩|Φ⁺⟩|Φ⁺⟩`, and above by `log_2 5` via the Schmidt rank, and states:

> Further we conjecture that $K_{AD:BC}(F_4)\leq 2$ by numerical results and
> thus have the following. The entanglement generation $K_{AD:BC}(F_4)=2$.
> Hence the entangling power of a four-qubit Fredkin gate $F_4$ is equal to
> two ebits.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevA.111.022407 (Crossref: published
  2025-02-07). The APS abstract page repeats the arXiv abstract ("in two to
  log₂5 ebits"); the published full text was not read.
- URL: https://arxiv.org/abs/2410.15253v1 (source retrieved 2026-09-29):
  `20241020_entangling_power_xinyu.tex`, Definition `def:N-ep` (l. 559–580),
  the gate `F_4` (l. 1146–1152) and Conjecture `coj:KAD:BC` (l. 1184–1191).
