---
slug: arunachalam-molina-russo-2013-hedging-majority-threshold
bibkey: arunachalam2017quantumhedging
doi: 10.4230/LIPIcs.TQC.2017.5
url: https://arxiv.org/abs/1310.7954v5
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/HedgingMajorityThreshold.result
---

# Bob cannot perfectly hedge more than n/2 of n parallel games

## Problem

S. Arunachalam, A. Molina and V. Russo, *Quantum hedging in two-round prover-verifier interactions*, arXiv:1310.7954v5, TQC 2017, LIPIcs 73 (2018) 5:1–5:30, Section 5:

> However, it still remains open to determine the conditions under which Bob can always win at least $k$ out of $n$ repetitions for some $k > 1$.

> Based on our current numerical evidence, it is possible that Bob cannot perfectly hedge more than $k = n/2$ games.

The game, the shared state u_α = α|00⟩ + √(1 − α²)|11⟩, Alice's measurement {P₀,θ, P₁,θ} with P₁,θ = v_θ v_θ* and v_θ = cos θ|00⟩ + sin θ|11⟩, and the parallel repetition with one joint channel Φₙ are quoted in [the literature note](../Library/QuantumContext/arunachalam2017quantumhedging.md).

Issue [#19590](https://github.com/the-omega-institute/trureturing/issues/19590) fixes the reading. Bob perfectly hedges k games if some channel on his n registers makes Alice record at least k wins with certainty. For all n and k with n < 2k ≤ 2n, all α ∈ (0, 1] and all θ, this is possible exactly when α² = cos²θ, that is, when a single game can already be won with certainty. The conjecture is proved.

## Motivation

The source characterizes when Bob can win at least one of n repetitions with certainty, which is the perfect-hedging phenomenon behind the failure of strong error reduction by parallel repetition for quantum interactive proofs. Its numerical programs become infeasible for larger k and n, and the threshold n/2 is suggested only by those computations. When k ≤ n/2, grouping one-out-of-two hedges gives perfect strategies for some parameters.

## Gap

The literature check before any Lean is recorded in #19590:
- arXiv v1–v5 all keep the open sentence;
- the citing work arXiv:2609.31223 cites the paper only to contrast hedging with winning all repetitions; the search seat reports that Molina's threshold theorem (arXiv:2008.07445) covers only k/n above the one-game optimum, and that the other citing records give no settlement;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Write c = cos θ, s = sin θ, β = √(1 − α²) and R = diag(α², β²), the reduced state of one game on Alice's retained qubit.
1. **Zero compression.** Let D = diag(s², −c²) and T = I ⊗ D on one game. Then v_θ* T v_θ = c²s² − s²c² = 0, so P₁,θ T P₁,θ = 0. Two outcome words with more than n/2 wins share a coordinate where both win. So the projector Π_k onto words with at least k wins satisfies Π_k T^{⊗n} Π_k = 0.
2. **Marginal.** Bob's channel acts only on his registers and is trace preserving, so the retained marginal of the returned state ρ is R^{⊗n}. Hence tr(T^{⊗n} ρ) = tr(D R)ⁿ = (α² s² − β² c²)ⁿ = (α² − c²)ⁿ.
3. **Support.** If tr(Π_k ρ) = 1, then ρ = Π_k ρ Π_k, because ρ is positive semidefinite with unit trace. Step 1 then gives tr(T^{⊗n} ρ) = 0, so α² = c².
4. **Converse.** If α² = c², a diagonal sign flip on Bob's side maps u_α to v_θ in every game, and Bob wins all n games.

## Falsifier

The proof would not settle the conjecture if the module's strategies were fewer than the source's, or its success notion weaker. The module:
- lets Bob apply an arbitrary channel on all n registers, given by a complete Kraus family Σ_l K_l* K_l = I, as in the source's Φₙ;
- measures each game with the source's P₀,θ and P₁,θ and counts wins game by game;
- requires certain success: the returned state has full weight on the projector onto words with at least k wins.

## Evidence

The canonical source is `D5/S3/Quantum/Information/HedgingMajorityThreshold.lean` (499 lines).
- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Registration.** The §3.9 registration is `Reg/D5/S3/Quantum/Information/HedgingMajorityThreshold.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/HedgingMajorityThreshold.lean.json`, statement `sha256:9649e3e88d763d43ba20571bc6e1ea7965bda5c4dad096b31ed8e61e5f067cec`.

Declaration statements:
- `result`: `sha256:4851dc25d0c439c0f5d5d73411b4c6d5f695bf74ead6381f1aa37fe577ae0636`;
- `claim`: `sha256:6257f01dbda091a08f2e893c8db2de658156951ba779a9f18b62aa55b918c85e`.

## Triage

Tier 1 question of a 2013 paper, preregistered in issue #19590 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: none`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for all n, k with n < 2k ≤ 2n, all α ∈ (0, 1] and all θ, a channel guaranteeing at least k wins exists if and only if α² = cos²θ.

**Computed, not formalized** (orchestrator, numpy, recorded in #19590): for n ≤ 5 and every k with 2k > n, Π_k T^{⊗n} Π_k = 0 and tr(D^{⊗n} R^{⊗n}) = (α² − cos²θ)ⁿ at random parameters.

**Argued, not formalized.**
- *Mechanism.* The observable T has zero expectation in the winning outcome of every single game, while its expectation is fixed by Alice's retained marginal, which Bob cannot touch. Majority winning sets are pairwise intersecting, so Π_k compresses T^{⊗n} to zero; a certain-majority strategy would make the fixed expectation (α² − cos²θ)ⁿ vanish.
- *Sharpness.* The threshold is exactly the intersecting-family threshold. At k ≤ n/2 two winning sets can be disjoint, the compression argument fails, and grouping one-out-of-two hedges gives perfect strategies for some α and θ.
- *Scope.* The argument uses only that P₁,θ has rank one and that the retained marginal is a product. It applies to any one-game measurement whose success projector is rank one with a vector of Schmidt rank two and whose retained marginal is fixed.

**Effect on the paper.** The suggested threshold holds for every n: Bob can never perfectly hedge more than n/2 of the games unless one game is already won with certainty. The paper's further questions, the exact conditions for k ≤ n/2 and the optimality of the grouping strategies, are not addressed.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The published proceedings text was not read; the quotations are from arXiv v5. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
