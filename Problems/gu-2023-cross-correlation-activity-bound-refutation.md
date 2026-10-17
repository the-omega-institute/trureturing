---
slug: gu-2023-cross-correlation-activity-bound-refutation
bibkey: gu2024crosscorrelationactivity
doi: 10.1103/PhysRevE.109.L042101
url: https://arxiv.org/abs/2312.00354v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.result
---

# The activity bound on cross-correlation asymmetry fails for general networks

## Problem

J. Gu, *Thermodynamic bounds on the asymmetry of cross-correlations with dynamical activity and entropy production*, Phys. Rev. E 109, L042101 (2024), arXiv:2312.00354, bounds the normalized asymmetry χ_ab = α_ab/√(D_a D_b) of the cross-correlation of two observables in a Markov jump process on N states.
- Eq. (8) bounds it by the dynamical activity A, the entropy production σ and the flux scale ratio γ: |χ_ab| ≤ γ/tan(π/N) · √(σ/(2A)).
- The author proves Eq. (8) for unicyclic networks and the weaker Eq. (9) in general, and writes: "We conjecture that Eq. (8) is valid for arbitrary networks". The evidence is 10⁶ random samples on three four-state topologies.

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/gu2024crosscorrelationactivity.md).

Issue [#18028](https://github.com/the-omega-institute/trureturing/issues/18028) fixes the reading: Eq. (8) holds for every N ≥ 3, every stationary network with bidirectional support and a positive flux, and all observables with D_a D_b > 0. This conjecture is refuted.

## Motivation

Eq. (8) would bound a measurable asymmetry of correlations by the total activity and the dissipation of an arbitrary network, giving an experimental lower bound on entropy production in terms of activity. The unicyclic case is proved; the general case is the conjecture.

## Gap

Issue #18028 records the literature check before any Lean:
- arXiv v1 and v2 and the journal version keep the conjecture;
- the full texts of three citing works (arXiv:2609.34352, 2606.05498 and 2410.20800) do not address Eq. (8) for general networks;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

1. **Network.** Sixteen states:
   - a hexagon 0 → 1 → ⋯ → 5 → 0 with forward rates 201/200 and backward rates 199/200;
   - the complete graph on {0, 6, …, 15} with all rates 1.

   The uniform distribution p = 1/16 is stationary, since every state has equal in- and out-rates.
2. **Observables.**
   - On the hexagon, (a, b) runs through the vertices of the regular hexagon.
   - On states 6, …, 15, a = 999/1000, …, 990/1000 and b = 0.
3. **Readings.**
   - γ = 201/199, A = 61/8 and σ = (3/800) ln(201/199);
   - α_ab = 3√3/3200, D_a = 300121/1600000 and D_b = 3/16;
   - so χ_ab² = 45/600242.
4. **Comparison.** cot(π/16) < 16/3, from tan x > x and π > 3, and ln(201/199) < 2/199. These give a bound B with B² < 62055936/865289770200 < 45/600242 = χ_ab².

## Falsifier

The refutation would not settle the conjecture if:
- the module's quantities differed from Eqs. (2)–(7);
- its network violated the source's assumptions.

The answers:
- **The quantities.** The module defines the one-way flux, the activity, the entropy production over positive fluxes, γ as the ratio of the largest to the smallest positive flux, α_ab and D_a exactly as in Eqs. (2)–(7).
- **The network.** It has bidirectional support, a stationary probability, positive fluxes on every edge, and observables with D_a D_b > 0. Missing edges are allowed by the source ("the transition between two states is either forbidden or bidirectional").

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.lean` (278 lines).
- It defines `flux`, `activity`, `entropyRate`, `scaleRatio`, `asym`, `diffusion`, `IsStationaryNetwork` and `claim`, and proves `result : ¬ claim`.
- It reuses `Probability` of `CycleSingleCutMinimax`, and Mathlib's bounds `Real.lt_tan`, `Real.pi_gt_three` and `Real.log_lt_sub_one_of_pos`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration: `result` is the designated refutation result of the `utility` header and is exempt; the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.lean.json`, statement `sha256:cb00d1491b609630adaccd4b9fb7bb7a7270f41a534956a48bb199f0858c6d66`.

Declaration statements:
- `result`: `sha256:8b78e91030f68a0718ae36e07021fccbc0a8f85e30f0d7a200476df231f04a3b`;
- `claim`: `sha256:1055d969a3cc4fe328b753d1d217e6be168c2e42b35146ce260d1cd328150c42`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #18028 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the network checks and the finite sums are rational computations with √3, and the comparison instantiates the tangent, π and logarithm bounds | open-problem-resolution |
| the network, sum and comparison helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** in the sixteen-state network above, |χ_ab| ≈ 0.008659 exceeds the bound of Eq. (8), ≈ 0.007963.

**Computed, not formalized** (orchestrator, SymPy, recorded in #18028):
- the stationary state is unique, since the kernel of the generator is one-dimensional;
- the proved bound Eq. (9), with N* = 61 nonzero local activities, evaluates to ≈ 0.0156 and holds.

**Argued, not formalized.**
- *Mechanism.* The clique adds activity without current. Its 55 edges carry total flux 55/8 of the activity A = 61/8, while their nearly equal observables add only 121/1600000 to D_a. The bound of Eq. (8) scales as 1/√A, so equilibrium activity attached to a driven cycle lowers the bound while χ_ab barely changes.
- *What survives.* The proved Eq. (9) carries the factor √N*, which grows with the number of edges; with N* = 61 it holds here. One possible correction of Eq. (8) for general networks is a dependence on the edges that carry no current.

**Open.** The smallest constant c_N for which |χ_ab| ≤ c_N γ √(σ/(2A)) holds for every network on N states.

**Effect on the paper.** Eq. (8) holds for unicyclic networks, as proved there, but not for arbitrary networks; Eq. (9) remains the general bound.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized", "Argued, not formalized" and "Open" are not formalized.
