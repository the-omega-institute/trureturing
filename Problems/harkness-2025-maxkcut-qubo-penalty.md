---
slug: harkness-2025-maxkcut-qubo-penalty
bibkey: harkness2025qubomaxkcut
doi: 10.48550/arXiv.2511.01108
url: https://arxiv.org/abs/2511.01108v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/MaxKCutQuboPenalty.result
---

# Tight penalty coefficients for the QUBO reformulations of max k-cut

## Problem

A. Harkness et al. (arXiv:2511.01108, quant-ph) study the penalty (QUBO)
reformulations of max k-cut used with QAOA, quantum annealers and Ising
machines. With edge weights of either sign, `d⁺_v` and `d⁻_v` the sums of the
positive and of the negative weights at `v`, the one-hot QUBO objective is
`q(x) = Σ_{uv∈E} w_uv (1 − Σ_j x_uj x_vj) − Σ_v c_v (Σ_j x_vj − 1)²`, and the
reduced R-QUBO objective on `k − 1` columns is
`q̄(x) = Σ_{uv∈E} w_uv (1 − Σ_j x_uj x_vj − (1 − Σ_j x_uj)(1 − Σ_j x_vj)) − Σ_v c_v Σ_{i<j} x_vi x_vj`.
The paper proves that every maximiser is an optimal k-cut when
`c_v > max(d⁺_v/k, −(3/2) d⁻_v)` (Theorem 1), respectively
`c_v > d⁺_v − 2 d⁻_v` (Theorem 2), and conjectures:

> Conjecture 1. Let G(V, E) be a graph with edge weights w_uv for all
> {u,v} ∈ E. Let x̂ ∈ {0,1}^{n×k} be an optimal solution of the QUBO
> formulation with c_v > max{d⁺_v/k, −d⁻_v/2} for every vertex v ∈ V. Then,
> x̂ is an optimal solution of the max k-cut problem.

> Conjecture 2. Let G(V,E) be a graph with edge weights w_uv for all
> {u,v} ∈ E. Let x̂ ∈ {0,1}^{n×(k−1)} be an optimal solution for the R-QUBO
> model with c_v > d⁺_v − d⁻_v for every vertex v ∈ V. Then, x̂ is an optimal
> solution of the max k-cut problem.

Issue #11239 fixes the reading. Vertices are `Fin n` and parts `Fin k`. The
weights are a symmetric real function, with weight 0 on non-edges, and the
edges are the pairs `u < v`. Matrices are Boolean, with entries read as 0 or 1.
"An optimal solution of the max k-cut problem" means feasible for the BQO
formulation (one-hot rows) and maximal for the BQO objective among feasible
points; for Conjecture 2 the same holds for the R-BQO formulation (rows with at
most one entry). The claim follows the paper's scope `k ≥ 3`.

## Motivation

The penalty coefficients control the energy landscape seen by QAOA and by
annealers, and the paper's experiments use the tightest valid values. Its
Appendices B and C show that smaller coefficients can fail, so the conjectured
values are the smallest of this form. The frozen declaration
`D5/S3/Quantum/Information/MaxKCutQuboPenalty.result` proves both conjectures.

## Gap

Issue #11239 preregisters the conjectures, the route and the literature check.
The latest version (v3, 2026-09-10) still states both conjectures and reports
no proof. INSPIRE-HEP and OpenAlex list no citing work (2026-09-29), and arXiv,
web and code searches found only the paper and the authors' code. The paper's
proofs move one vertex at a time; at the Conjecture 1 threshold there are
infeasible points that no single-vertex change improves, so that method cannot
reach the conjectured constants.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

Let `t_v` be the number of parts of `v` in a maximiser `x̂`, and `V₂` the set of
vertices with `t_v ≥ 2`.

1. **Averaged deletion (Conjecture 1).** For each colour `j`, delete `j` from
   every vertex of `V₂`. Summed over all colours, the objective changes by
   `Σ_{v∈V₂} c_v t_v(2t_v − 3) + Σ_{u<v touching V₂} w_uv m_uv`, where `m_uv`
   is the number of shared colours.
   - For such an edge, `m_uv ≤ (φ_u + φ_v)/2` with `φ_v = t_v(2t_v − 3)` on
     `V₂` and 0 elsewhere.
   - Dropping the positive weights and regrouping the negative ones by vertex,
     the change is at least `Σ_{v∈V₂} (c_v + d⁻_v/2) φ_v > 0`.
   - Hence some deletion improves `x̂` unless `V₂` is empty.
2. **Empty vertices.** If `t_v = 0`, giving `v` the colour `i` changes the
   objective by `c_v − Σ_u w_uv x̂_ui`. Summed over `i`, this is at least
   `k c_v − d⁺_v > 0`.
3. **Conjecture 2.** The same deletion on the `k − 1` columns saves
   `c_v s_v(s_v − 1)` in penalty and changes each edge term by at most
   `s_u(s_u − 1) + s_v(s_v − 1)` in absolute value. The gain is at least
   `Σ_{v∈V₂} (c_v − d⁺_v + d⁻_v) s_v(s_v − 1) > 0`.
4. On feasible points the penalties vanish, so a maximiser that is feasible
   maximises the BQO (respectively R-BQO) objective among feasible points.

## Falsifier

The answer would change if the edges were counted with multiplicity or the
weights were not symmetric, or if "optimal solution of the max k-cut problem"
required something other than feasibility and maximal cut weight among
feasible points.

## Evidence

Exact enumeration (issue #11239), with random weights in
`{±1, ±2, ±3}/{1, 2}` and penalties at the threshold plus `1/1000`:
- no counterexample to Conjecture 1 for `(n, k) = (3, 3), (4, 3), (4, 2)`, and
  none to Conjecture 2 for `(n, k) = (3, 3), (4, 3), (3, 4)`;
- the controls with `−d⁻/3` and `d⁺ − d⁻/2` fail in 61–206 of the 100–300
  instances per case.

The canonical source is
`D5/S3/Quantum/Information/MaxKCutQuboPenalty.lean`. Its public declarations
are `ind`, `dplus`, `dminus`, `cutValue`, `quboObjective`, `OneHot`,
`reducedCutValue`, `reducedQuboObjective`, `AtMostOneHot`,
`quboPenaltyConjecture`, `reducedQuboPenaltyConjecture`, `claim`, and
`result`. The frozen module state has statement identity
`sha256:bb3246bc7c98be50402376fc200f0a8971b2e59d50faf5524c8199b08abd3e44`.
The result declaration has statement identity
`sha256:bb1ca90f8ec91863b25d60270f7f45f0be2151e671411478e51feba50b94ba7d`.
The Freeze event is
`sha256:a68fc0471de795ed2107c3ffad2fd266b21cf8311c5bd1d8cadaed3e6998e9a3`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjectures, preregistered in issue #11239 before any
Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the averaged deletion and insertion moves, the edge
bounds and the regrouping by vertex are proved in the module. Its escape
witness is form (2), the public conclusion itself, and its admission basis is
`open-problem-resolution`. Utility `none`: the statement holds for all graphs
and weights.

## ASSUMED-UNVERIFIED

The proof does not use the paper's scope `k ≥ 3`; the formal statement keeps it.
The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
