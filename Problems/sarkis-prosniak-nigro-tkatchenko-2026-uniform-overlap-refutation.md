---
slug: sarkis-prosniak-nigro-tkatchenko-2026-uniform-overlap-refutation
bibkey: sarkis2026starbattery
doi: 10.48550/arXiv.2603.10853
url: https://arxiv.org/abs/2603.10853v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.result
---

# A 1225-vertex graph refutes the star bound on the minimal-energy uniform overlap of quantum batteries

## Problem

M. Sarkis, O. A. Prośniak, S. Nigro and A. Tkatchenko, *Star Topology Optimizes the Charging Power of Quantum Batteries*, arXiv:2603.10853v1, study a battery of N fermionic cells coupled along a graph G.
- **Overlaps and mode energies.** The adjacency matrix A has orthonormal eigenvectors u_k with eigenvalues ε_k and uniform overlaps w_k = (1ᵀu_k)² (Eq. (11)). With a local field h, the mode energies are E_k(h) = (N/M)ε_k + h (Eq. (14)).
- **The charging power.** It is a weighted mean of the w_k, and the authors single out w_min = Σ_{k′} w_{k′} over the modes of least energy.
- **The star.** It gives w_min(S) = N/2 − √(N − 1) (Eq. (23)).
- **The conjecture.** "Conjecture 1 (Star optimality for the uniform overlap). Let G be a non-empty graph on N vertices. Its minimal energy uniform overlap w_min(G) is upper bounded by w_min(G) ≤ w_min(S) = N/2 − √(N − 1)." The authors base it on an exhaustive check for N ≤ 7 and random samples.

The verbatim statements are in [the literature note](../Library/GraphInvariants/sarkis2026starbattery.md).

Issue [#16578](https://github.com/the-omega-institute/trureturing/issues/16578) fixes the reading.
- Because E_k(h) is increasing in ε_k, w_min(G) is the squared length of the projection of 1 onto the lowest adjacency eigenspace.
- "Non-empty" means at least one edge.
- The conjecture is refuted.

## Motivation

The conjecture was the authors' primary evidence that the star stays optimal for the charging power in a non-zero local field (§III.C). A graph whose lowest mode carries a larger uniform overlap than the star's removes that support.

## Gap

Issue #16578 records the literature check before any Lean:
- arXiv v1 is the only version;
- Semantic Scholar lists no citing work;
- Zenodo and web search return no settlement;
- the repository had no entry for the paper.

The graph operation, the q-triangulation, is that of Zeng–Zhang (arXiv:1808.01025), whose results concern other spectral quantities.

`not-found-in-searched-scope`.

## Route

Let G_m be the q-triangulation of K_m with q = 3(m − 1). It is the complete graph on m core vertices together with, for every pair {i, j} of core vertices, q new vertices adjacent exactly to i and j. Its vertex count is N = m + 3m(m − 1)²/2.

1. **The eigenvector.** v is 1 on the core and −1/(m − 1) on the attached vertices, and Av = −2(m − 1)v.
2. **The least eigenvalue.** Write the core values as x_i and the attached values as y, with S = Σx_i.
   - Each attached y at {i, j} gives 2(m − 1)y² + 2y(x_i + x_j) ≥ −(x_i + x_j)²/(2(m − 1)).
   - With Σ_{i<j}(x_i + x_j)² = (m − 2)Σx_i² + S², this gives xᵀ(A + 2(m − 1)I)x ≥ (m/2)Σx_i² − S²/2 ≥ 0, by Cauchy–Schwarz.
   - So λ_min = −2(m − 1).
3. **The overlap.** v lies in the least eigenspace, so w_min ≥ (1ᵀv)²/‖v‖² = m(3m − 5)²/10.
4. **The violation.** This exceeds N/2 exactly when 3m² − 30m + 25 > 0, that is, for m ≥ 10. At m = 10: N = 1225, λ_min = −18, 1ᵀv = −125, ‖v‖² = 25, and w_min ≥ 625 > 612.5 > 1225/2 − √1224.

## Falsifier

The refutation would not hold if:
- the module's w_min differed from the source's;
- its graphs were not the source's simple unweighted graphs;
- the witness were empty or not simple.

The module defines w_min as 1ᵀE_{λ_min}1 with the repository's spectral projector E_θ, the sum of u uᵀ over an orthonormal eigenbasis with eigenvalue θ. That is the source's Σ_{k′}(1ᵀu_{k′})². The witness is a simple graph with 1225 vertices and at least one edge.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.lean` (382 lines).
- It defines `lamMin`, `wmin` and `claim`, and proves `result : ¬ claim` with the witness G₁₀ on `Fin 1225`, built on the structured vertex type and transported by an explicit equivalence.
- It uses the frozen `idempotent` of `D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum` and the frozen `eig_dot_zero` of `D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees` (an eigenbasis vector with a different eigenvalue is orthogonal to an eigenvector), with pinned Mathlib spectral theory (`Matrix.IsHermitian.eigenvectorBasis`), Cauchy–Schwarz and `Equiv.sum_comp`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.lean.json`, statement `sha256:b89305408fbce1df2448c6f05d2cb273221f6e8727804131b316849b8caec6d9`.

Declaration statements:
- `result`: `sha256:e04fd52d43e23960ad30b1b413c48167eb8a750431f5797a78f8cbe0fea81632`;
- `claim`: `sha256:e2463769c94184ce5d3794b268f0feb5d0211d08c02febedc5ebdc10e78c90d4`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #16578 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the witness, its eigen-equation, the quadratic-form certificate and the overlap bound are instantiations of pinned Mathlib and frozen D5 results followed by normalization | open-problem-resolution |
| the overlap, graph, eigenvector, incidence, quadratic-form and transport helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** Conjecture 1 fails: the q-triangulation of K₁₀ with q = 27 has w_min ≥ 625, while the bound is 1225/2 − √1224 ≈ 577.5.

**Computed, not formalized** (orchestrator, NumPy, 14 October 2026):
- for G₁₀ the least eigenvalue is −18.0000 with a one-dimensional eigenspace, and w_min = 625.0000 exactly;
- within the q-triangulation family, violations already occur at (m, q) = (6, 5) with N = 81, where the lowest eigenspace has multiplicity 6, and at (6, 6) with N = 96, where it is simple and the eigenvalue is irrational;
- no violation occurs among all graphs with N ≤ 7, nor among 16,800 random graphs with 8 ≤ N ≤ 14, consistent with the source's checks;
- control: the stars K₁,₄ and K₁,₈ attain the bound exactly.

**Argued, not formalized.**
- The whole family G_m with m ≥ 10 refutes the conjecture, with w_min(G_m)/N → 3/5 against 1/2 for the star. The overlap therefore exceeds the star's value by a constant fraction of N, not merely by an O(√N) term.
- The mechanism: the least eigenvector takes the same sign, −1/(m − 1), on every attached vertex, and the attached vertices form almost all of the graph. Its uniform overlap is therefore a constant fraction of N.

**Open.**
- The smallest N for which Conjecture 1 fails. The source checks N ≤ 7, and the smallest known violation is N = 81.
- Whether the star still maximizes the charging power R_G(h) itself, which is a weighted mean that w_min does not determine.

**Effect on the paper.** Conjecture 1 is false, so it cannot serve as evidence for the star's optimality at non-zero field. The zero-field Theorem 1 is unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
