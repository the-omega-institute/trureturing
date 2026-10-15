---
slug: reda-sacchi-macchiavello-guarnieri-2026-dynamic-cooling-tie-uniqueness
bibkey: reda2026dynamiccooling
doi: 10.48550/arXiv.2607.23641
url: https://arxiv.org/abs/2607.23641v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.result
---

# Global dynamic cooling strictly beats equal parallel groups except at (N, M) = (6, 2)

## Problem

M. Reda, M. Sacchi, C. Macchiavello and G. Guarnieri, *Optimal Dynamic Cooling of Multiple Qubits*, arXiv:2607.23641v1, cool the first M of N identical thermal qubits, in the state ρ = τ^{⊗N} with τ = diag(1 − P₁, P₁), by one global unitary. The aim is the lowest common local temperature: every target must end with the same diagonal one-qubit marginal. The optimum is p_glob(N, M; P₁) = p★(N, M; P₁).

§IX compares it with M disjoint groups of n = ⌊N/M⌋ qubits, each running the optimal n-qubit single-target protocol: p_par(N, M; P₁) = p★(n, 1; P₁) (Eqs. (88)–(89)). The source proves p_glob ≤ p_par, strictness for M + 2 ≤ N ≤ 3M − 1 (Eq. (91)), and the tie p_glob(6, 2) = p_par(6, 2) = 3P₁² − 2P₁³ (Eq. (92)). It then writes: "Exact symbolic checks over the finite range investigated revealed no other equality, although the uniqueness of this tie remains a conjecture." The verbatim statements are in [the literature note](../Library/QuantumChannels/reda2026dynamiccooling.md).

Issue [#16483](https://github.com/the-omega-institute/trureturing/issues/16483) fixes the reading: for all M ≥ 2, N ≥ M + 2 with (N, M) ≠ (6, 2), and every 0 < P₁ < 1/2, p_glob(N, M; P₁) < p_par(N, M; P₁). It is proved. The tie (92) is the source's and is not re-proved here.

## Motivation

The comparison decides when joint control of the whole register is worth its cost over independent single-target refrigerators. The source settled only the window N ≤ 3M − 1 and a finite range of sizes.

## Gap

Issue #16483 records the literature check before any Lean:
- arXiv v1 is the only version;
- Semantic Scholar lists no citing work;
- the Pith review page lists the uniqueness of the (6, 2) tie among its "Open items";
- Zenodo and web searches return no settlement;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

1. **The cutoff.** For a diagonal state λ, any unitary V and an output set R, write a_j = Σ_{i∈R} |V_ij|². Then 0 ≤ a_j ≤ 1 and Σ a_j = |R|, so the probability of R after V is at least the sum of λ over any set H of size |R| that is separated from its complement by a threshold. No sorting or Birkhoff decomposition is needed.
2. **The parallel benchmark.** Take the hot half H_n of the n-bit strings: weight above n/2, or weight n/2 with first bit 1. The cutoff gives p★(n, 1; P₁) ≥ p_n, the thermal weight of H_n.
3. **The global unitary.** Split the register as M groups of n qubits plus r = N mod M unused ones.
   - A permutation applies the complement-pair cooling map in every group, so every target has population exactly p_n.
   - A real reflection then exchanges the equal superposition u of the M strings e_i, each with only target i excited and weight k = ⌈n/2⌉, with one all-ground string v of weight K = M⌊n/2⌋ + r. Both strings are fixed by the permutation.
   - The state becomes σ + (q_k − q_K)(vvᵀ − uuᵀ), with q_j = P₁^j (1 − P₁)^{N−j}. Every target marginal stays diagonal, with population p_n − (q_k − q_K)/M.
4. **The arithmetic.** K > k for every admissible pair except (6, 2), where n = 3, M = 2, r = 0 and K = k = 2. Since q_j is strictly decreasing for 0 < P₁ < 1/2, the reflection lowers every target strictly.

## Falsifier

The proof would not settle the conjecture if:
- the module's feasible set were weaker than "every target marginal equals diag(1 − g, g)";
- its infimum ranged over fewer unitaries than the source's;
- its benchmark differed from p★(⌊N/M⌋, 1).

The module requires population g and coherence 0 for each target. The trace gives the (0,0) entry 1 − g and Hermiticity the (1,0) entry, so the marginal is exactly diag(1 − g, g). The infimum ranges over every complex unitary of the register.

## Evidence

The canonical source is `D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.lean` (894 lines).
- It defines `tau`, `thermalWeight`, `rho`, `population`, `coherence`, `feasible`, `pGlob` and `claim`, and proves `result : claim`.
- It uses the frozen `projected_dynamics_is_unistochastic` of `D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics` for the diagonal readout of a unitary conjugation and the double stochasticity of |U_ij|², and the frozen `sum_prod_update` of `D5/S3/Entropy/NamingWindow/SumProductUpdate` for the product-sum factorization. It also uses pinned Mathlib, including `strictAntiOn_Iic_of_succ_lt`, for permutation matrices, `vecMulVec` algebra, `finProdFinEquiv` and `finSumFinEquiv`, and `csInf_le`/`le_csInf`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.lean` reads out the parallel benchmark `pGlob (N / M) 1 P₁` of `claim`. Its rejected realization replaces the benchmark by the global value itself, and its Law fails by irreflexivity at (N, M, P₁) = (4, 2, 1/4). It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Thermal/DynamicCoolingParallelTieUniqueness.lean.json`, statement `sha256:474242d9b04e0e21987c982eb39802596c6d3b059269f4b0316c44ebdf41d6b4`.

Declaration statements:
- `result`: `sha256:7411a2eaaf9da6028a6310ffb7f496e016dec61de39920b0a166cae71579d0dc`;
- `claim`: `sha256:2d8110d610928f9dd0cf09a4ae1782c6cf91fddff41ac8273daa1d8d6d81da5a`.

## Triage

Tier 1 conjecture of a 2026 paper, preregistered in issue #16483 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the explicit witness, the cutoff and the arithmetic are instantiations of pinned Mathlib and frozen D5 results followed by normalization | open-problem-resolution |
| the cutoff, threshold, hot-set, cooling-permutation, grouping, reflection, marginal, witness and arithmetic helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed.

The utility is `none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`.** For every admissible pair other than (6, 2), the global optimum lies strictly below the parallel benchmark at every temperature. The proof gives the explicit margin p_par − p_glob ≥ (q_k − q_K)/M with k = ⌈n/2⌉ and K = M⌊n/2⌋ + (N mod M).

**Established inside the proof.**
- The single-target lower bound p★(n, 1; P₁) ≥ p_n holds against every complex unitary.
- The block-wise complement-pair permutation attains p_n in every group at once.

**Computed, not formalized** (orchestrator, exact rational arithmetic, 14 October 2026):
- the source's passive formula, Eqs. (12)–(15), gives p★(N, M) = p★(⌊N/M⌋, 1) only at (6, 2) among the 275 cases with M ≥ 2, N ≥ M + 2, N ≤ 13 and P₁ ∈ {1/10, 1/4, 1/3, 2/5, 49/100};
- the margin above is respected in every case.
- the coherent step is needed: at (N, M) = (4, 2) and P₁ = 1/10, every computational-basis permutation with equal target populations leaves the common population at least 1/10 = p_par. This is an exact enumeration of the 102 equal-population assignments of the eigenvalue shells to the four target patterns.

**Argued, not formalized.**
- The obstruction is a shell coincidence. At (6, 2) the single-excitation strings and the all-ground string reachable by one swap share the shell k = K = 2, so no coherent exchange lowers the targets. At every other admissible pair the all-ground string sits in a strictly colder shell.

**Open.**
- The exact gap p_par − p_glob for general (N, M).
- Whether some other benchmark partition (unequal groups, or using the unused qubits) also ties only at finitely many pairs.

**Effect on the paper.** The uniqueness conjecture of §IX is a theorem, and the tie (92) is the only nontrivial equality for every register size.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
