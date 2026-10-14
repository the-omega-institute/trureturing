---
slug: myhill-blumenfeld-2023-granular-steady-state-uniqueness-refutation
bibkey: myhill2023granularsteadystates
doi: 10.1088/1751-8121/ace56d
url: https://arxiv.org/abs/2306.10526v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.result
---

# The cell-order dynamics of two-dimensional granular systems can have two physical steady states

## Problem

A. D. C. Myhill and R. Blumenfeld, *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*, J. Phys. A 56, 345001 (2023), arXiv:2306.10526v2, study the evolution of the cell-order distribution Q_3, …, Q_C of a two-dimensional granular packing.
- **The dynamics.** Cells of orders i and j merge into a cell of order i + j − 2 at rate p_{i,j}, and split back at rate q_{i,j}; the net flux of the process is η_{i,j} = p_{i,j}Q_iQ_j − q_{i,j}Q_{i+j−2} (§I.A). Eq. (1) gives Q̇_k as the gain from processes producing k-cells, minus the loss from processes consuming them, plus Q_k Σ η, the renormalization for the changing number of cells.
- **What is proved there.** A detailed-balance steady state (every η_{i,j} = 0) is unique when it exists; for C = 6 and C = 7 no other steady state exists when it does.
- **The conjecture.** "Based on these investigations, we conjecture that, for any choice of constant rates, there is only one physical solution regardless of the upper order, C" (§I.D), where a physical solution has every Q_k real and positive (§III).

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/myhill2023granularsteadystates.md).

Issue [#16957](https://github.com/the-omega-institute/trureturing/issues/16957) fixes the reading:
- every C ≥ 3, every assignment of strictly positive constant rates to the processes 3 ≤ i ≤ j with i + j − 2 ≤ C, and normalized positive states;
- stationarity is the vanishing of the full right-hand side of Eq. (1), read with the flux of §I.A;
- the printed loss term of Eq. (1) is read as η_{k,i−k+2}, whose splitting factor is the product cell Q_i, as in Eq. (2).

The conjecture is refuted at C = 10.

## Motivation

The paper connects uniqueness to experiments in which sheared granular packings always settle into detailed-balance steady states. Uniqueness for every choice of constant rates would make the steady state a function of the rates alone. The refutation shows that already for constant positive rates the steady state can depend on the initial condition.

## Gap

Issue #16957 records the literature check before any Lean:
- arXiv v1–v2; v2 states the conjecture in §I.D and §III;
- the citing works read (Krengel, arXiv:2502.06085) or reported by the search seat (Sun–Wang–Wang–Blumenfeld–Zhang 2025; Wanjura et al., arXiv:2404.05059v2) give no proof and no counterexample;
- a web search and Zenodo found no related settlement; Semantic Scholar was unavailable (HTTP 429);
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

Take C = 10, with its sixteen processes ordered (3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (4,4), (4,5), (4,6), (4,7), (4,8), (5,5), (5,6), (5,7), (6,6).
- Rates: p = (10/3, 2/3, 4/15, 4/3, 2/3, 2, 509018/225, 1, 35579/175, 2, 422/5, 2, 386/225, 30416/25, 255689/25, 4) and q = (1, 2/5, 2, 972/5, 2, 2, 2138/75, 141/10, 1, 2, 2, 3967/35, 35878/315, 2, 233557/35, 2), all positive.
- States, in orders 3 to 10: X = (3, 2, 5, 1, 2, 1, 1, 1)/16 and Y = (12, 6, 5, 4, 4, 1, 1, 1)/34. Both are positive and normalized, and X_3 = 3/16 ≠ 6/17 = Y_3.

Then:
1. **The C = 10 equations.** For arbitrary rates and states, the right-hand side of Eq. (1) at k ∈ {3, …, 10} is a balance row (the gain minus the loss, with the δ-factors) plus Q_k times the total flux over the sixteen processes. This identity is derived from the general definition.
2. **The certificates.** At X and at Y, the total flux and all eight balance rows vanish, by exact rational arithmetic.
3. **The contradiction.** Both are physical steady states of the same positive rates, and they differ at k = 3.

## Falsifier

The refutation would not hold if:
- the module's process set differed from the source's (3 ≤ i ≤ j, i + j − 2 ≤ C), or its flux, gain, loss or δ-factors differed from Eqs. (1)–(2);
- its notion of a physical state were weaker than the source's real positive normalized fractions;
- the C = 10 equations were asserted rather than derived from the general right-hand side.

The module defines the process set as a filter of `Finset.Icc 3 C ×ˢ Finset.Icc 3 C`, writes the right-hand side for general C with the three sums of Eq. (1), requires every rate positive, every Q_k positive and Σ_k Q_k = 1, and proves the C = 10 expansion for arbitrary rates and states.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.lean` (270 lines).
- It defines `J`, `delta`, `flux`, `rhs`, `PositiveRates`, `Physical`, `Stationary` and `claim`, and proves `result : ¬ claim` at C = 10.
- It uses pinned Mathlib only: `Finset.sum_Icc_succ_top`, finite-set sums and `interval_cases`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- `result` is the refutation result of a `refutes` utility, which CLAUDE.md §3.9 exempts from four-slot registration.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.lean.json`, statement `sha256:1f6d77962776552fdf3dee66e16cb484ed852a8723a1183a9ffb7796b5ce1452`.

Declaration statements:
- `result`: `sha256:eab62f00e1ca864de25f61faf48957de4502c17fdf6fc8b7215a1a0276faff46`;
- `claim`: `sha256:48209a297366fd56e6ec2f3dd2cf844ec431a5ea71dddfd3b8d96089b5fa9c15`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #16957 before any Lean.
`counterexample`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the C = 10 expansion of the general right-hand side and the two rational certificates are interval-sum rewriting followed by normalization | open-problem-resolution |
| the rate and state tables and the expansion, positivity, physicality, balance and stationarity helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `certified-instance` with basis `refutes` the module's `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for C = 10 and the positive rates above, the cell-order dynamics has two distinct physical steady states; the uniqueness conjecture fails.

**Computed, not formalized** (orchestrator, Python and mpmath, 15 October 2026):
- The two states are stationary under the full Eq. (1) by exact rational arithmetic, with Σ η = 0 at both; neither satisfies detailed balance, and no detailed-balance state exists for these rates, since θ_{3,3}θ_{4,4} = 100/423 ≠ 2/9 = θ_{3,4}θ_{3,5} with θ = p/q.
- For the same rates, multistart root finding followed by 50-digit Newton refinement (residual below 10⁻⁴⁸) finds a third physical steady state, approximately (0.43995, 0.50554, 0.0050850, 0.044208, 0.0041825, 0.00048549, 0.00045463, 0.000099506).
- Already at C = 8, the largest order of the paper's numerical tests, rates drawn log-uniformly from [10⁻³, 10³] give systems with two and with three physical steady states (4 of 800 random systems; two instances confirmed by 50-digit refinement). No multiplicity was found at C = 6 or C = 7 (1,500 systems each), or at C = 6 and C = 8 with rates in [10⁻¹, 10] (1,500 and 800 systems).

**Argued, not formalized.**
- The mechanism is the cycle structure of the processes. For C ≥ 6 the steady-state equations leave the fluxes underdetermined (§I.C), and a non-detailed-balance steady state carries circulating fluxes through cycles such as 4 + 4 → 6 → 3 + 5 → 6. With rates spread over several orders of magnitude, these cycles allow several positive balances of the same polynomial system. The paper's numerical tests used rates differing by at most a factor of 30 ({0.1, 0.5, 1.0, 3.0} at C = 6, pairs within {0.1, 0.5, 1, 2} at C = 7 and C = 8).
- The paper's proved results are unaffected: uniqueness of the detailed-balance state when one exists, and the cases C = 6, 7 with a detailed-balance state.

**Open.**
- Whether every system with C ≤ 7 has a unique physical steady state.
- Whether multiplicity can occur for rates within the factor-30 range of the paper's tests, and which steady state the dynamics selects from a given initial condition.

**Effect on the paper.** The conjecture of §I.D and §III fails, so the uniqueness of steady states cannot explain the experimental convergence to a unique state for arbitrary constant rates; the paper's alternative explanation, rates that self-organize towards detailed balance, is not affected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" (beyond the exact check of X and Y) and "Argued, not formalized" are not formalized.
