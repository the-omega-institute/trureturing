---
bibkey: harkness2025qubomaxkcut
authors: Adrian Harkness; Hamidreza Validi; Ramin Fakhimi; Illya V. Hicks; Samuel Stein; Tamás Terlaky; Luis F. Zuluaga
year: 2025
title: "Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing"
doi: 10.48550/arXiv.2511.01108
url: https://arxiv.org/abs/2511.01108v3
claim: "For max k-cut with real edge weights, every optimal solution of the one-hot QUBO reformulation is an optimal k-cut when c_v > max(d+_v/k, -(3/2) d-_v) (Theorem 1), and of the reduced R-QUBO reformulation when c_v > d+_v - 2 d-_v (Theorem 2); Conjectures 1 and 2 state the same for c_v > max(d+_v/k, -d-_v/2) and for c_v > d+_v - d-_v."
strata_touched:
  - D5/S3/Quantum/Information/MaxKCutQuboPenalty
license: citation-only
triage: anchor
---

# Characterizing QUBO Reformulations of the Max-k-Cut Problem for Quantum Computing

A. Harkness, H. Validi, R. Fakhimi, I. V. Hicks, S. Stein, T. Terlaky and
L. F. Zuluaga, arXiv:2511.01108 (v1 2025-11-02, v2 2026-05-11, v3 2026-09-10).
Subjects: quant-ph (primary), cs.ET.

The paper studies the penalty (QUBO, i.e. Ising) reformulations of max k-cut
used with QAOA, quantum annealers and Ising machines. For a graph `G(V, E)`
with real edge weights, write `d⁺_v` and `d⁻_v` for the sums of the positive
and of the negative weights at `v`. The BQO formulation maximises
`Σ_{uv∈E} w_uv (1 − Σ_j x_uj x_vj)` subject to `Σ_j x_vj = 1`, and its QUBO
reformulation is

> q(x) = Σ_{{u,v}∈E} w_uv (1 − Σ_{j∈P} x_uj x_vj) − Σ_{v∈V} c_v (Σ_{j∈P} x_vj − 1)².

The reduced R-BQO formulation uses `k − 1` columns with `Σ_j x_vj ≤ 1`, and its
R-QUBO reformulation penalises `Σ_{i<j} x_vi x_vj`. The paper proves exactness
for `c_v > max(d⁺_v/k, −(3/2) d⁻_v)` (Theorem 1) and for
`c_v > d⁺_v − 2 d⁻_v` (Theorem 2), and conjectures (§3.1 and §3.2):

> Conjecture 1. Let G(V, E) be a graph with edge weights w_uv for all
> {u,v} ∈ E. Let x̂ ∈ {0,1}^{n×k} be an optimal solution of the QUBO
> formulation with c_v > max{d⁺_v/k, −d⁻_v/2} for every vertex v ∈ V. Then,
> x̂ is an optimal solution of the max k-cut problem.

> Conjecture 2. Let G(V,E) be a graph with edge weights w_uv for all
> {u,v} ∈ E. Let x̂ ∈ {0,1}^{n×(k−1)} be an optimal solution for the R-QUBO
> model with c_v > d⁺_v − d⁻_v for every vertex v ∈ V. Then, x̂ is an optimal
> solution of the max k-cut problem.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2511.01108
- URL: https://arxiv.org/abs/2511.01108v3 (full text of v3 retrieved
  2026-09-29).
- Location: §2 for the BQO and R-BQO formulations and the scope `k ≥ 3`
  (Remark 1); §3 for `d⁺_v`, `d⁻_v`, the QUBO and R-QUBO objectives,
  Theorems 1 and 2 and Conjectures 1 and 2; Appendices B and C for the
  examples showing that smaller coefficients can fail.
