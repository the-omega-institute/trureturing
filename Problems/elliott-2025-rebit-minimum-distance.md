---
slug: elliott-2025-rebit-minimum-distance
bibkey: elliott2025complex
doi: 10.1103/PhysRevA.111.062401
url: https://arxiv.org/abs/2505.16523v2
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/RebitExclusionDistance.result
---

# The minimum average trace distance of a rebit strategy for Elliott's exclusion task is exactly 1/12

## Problem

T. J. Elliott, *Strict advantage of complex quantum theory in a communication task*, arXiv:2505.16523v2, Phys. Rev. A **111**, 062401 (2025), studies a four-input task with target distribution P(y|x) = (1 − δ_xy)/3 on X = Y = {0, 1, 2, 3}. A complex qubit realizes it exactly, while no real qubit (rebit) strategy does. For the robustness of this separation the source measures the error by d = (1/|X|) Σ_x (1/2) Σ_y |P(y|x) − P̃(y|x)|. It shows that d = 1/12 is achievable with a rebit (Appendix D), and writes: "We therefore only weakly conjecture that d = 1/12 the the minimum distance for a rebit strategy." The verbatim statements are in [the literature note](../Library/Quantum/elliott2025complex.md).

Issue [#16523](https://github.com/the-omega-institute/trureturing/issues/16523) fixes the reading. A rebit strategy is:
- four real symmetric positive-semidefinite 2 × 2 states of trace 1;
- a four-outcome POVM of real symmetric positive-semidefinite effects summing to the identity.

Mixed states and POVMs cover private randomness and post-processing on either side. The claim is that 1/12 is the least distance attained by such strategies. It is proved.

## Motivation

The exact minimum turns the qualitative real–complex separation into a quantitative one. Under the source's resource assumptions — a two-dimensional message, no shared randomness and no correlations between rounds — any experiment that reaches average trace distance below 1/12 from the target certifies that the messages carry imaginarity.

## Gap

Issue #16523 records the literature check before any Lean:
- arXiv v2 is the latest version and keeps the conjecture; the journal version is Phys. Rev. A 111, 062401;
- Heinosaari–Kerppo (arXiv:1903.04899v2, Example 6) show that a rebit cannot realize this communication matrix, but compute no distance;
- the citing works arXiv:2506.08091v1, arXiv:2509.03004v1 and arXiv:2507.14878v1 contain no rebit-distance optimum;
- Zenodo, Crossref and web search return no settlement.

`not-found-in-searched-scope`.

## Route

1. **Linear dependence.** Real symmetric 2 × 2 matrices form a three-dimensional space, so the four states satisfy Σ_x w_x ρ_x = 0 for some real w ≠ 0. Taking traces gives Σ_x w_x = 0.
2. **Two identities.** For every outcome y, Σ_x w_x tr(ρ_x E_y) = 0 by linearity, while Σ_x w_x P(y|x) = −w_y/3.
3. **The L¹ estimate.** With Δ_xy = tr(ρ_x E_y) − P(y|x) and m = max_x |w_x| > 0, each y gives |w_y|/3 ≤ m Σ_x |Δ_xy|. Summing over y, and using Σ_x |w_x| ≥ 2m (which follows from Σ_x w_x = 0), gives Σ_{x,y} |Δ_xy| ≥ 2/3, that is d ≥ 1/12.
4. **Attainment.** The strategy below, written as states and a rebit POVM, has d = 1/12. With r = √3:
   - the states are ρ₀ = diag(1, 0), ρ₁ = (1/4)[[1, −r], [−r, 3]] and ρ₂ = ρ₃ = (1/4)[[1, r], [r, 3]];
   - the POVM is E₀ = (1/9)[[0, 0], [0, 4]], E₁ = (1/9)[[3, r], [r, 1]], E₂ = (1/9)[[3, −r], [−r, 1]] and E₃ = I/3.

   This is the source's strategy of Appendix D: the three dilated basis outcomes reported with probability 2/3, and the output 3 otherwise. It realizes the target except that the row for x = 3 equals the row for x = 2.

## Falsifier

The proof would not settle the conjecture if:
- the module's strategies were fewer than the source's rebit strategies;
- its distance differed from the source's d.

Both checks pass:
- Every rebit strategy of the source is a family of real states and one real POVM: mixed states cover Alice's randomness; Bob's randomness, post-processing and dilated measurements compress to a POVM on the rebit; and there is no shared randomness.
- The module's distance is (1/4) Σ_x (1/2) Σ_y |P(y|x) − tr(ρ_x E_y)|.

## Evidence

The canonical source is `D5/S3/QuantumBounds/RebitExclusionDistance.lean` (231 lines).
- It defines `target`, `IsRebitStrategy`, `dist` and `claim`, and proves `result : claim`.
- It uses pinned Mathlib for linear independence and finite rank (`LinearIndependent.fintype_card_le_finrank`, `Module.finrank_fin_fun`, `Fintype.not_linearIndependent_iff`), positive-semidefinite outer products (`Matrix.posSemidef_vecMulVec_self_star`), trace linearity and finite-sum triangle inequalities. It has no frozen D5 dependency.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration in `Reg/D5/S3/QuantumBounds/RebitExclusionDistance.lean` reads out the least value 1/12 of `claim`. Its rejected realization, the value 0, fails because the attained distance 1/12 would have to be at most 0. It is `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/QuantumBounds/RebitExclusionDistance.lean.json`, statement `sha256:176a14f8a85d0d495f5156ebc476f9e348705847ac91e1222788f0904c7db668`.

Declaration statements:
- `result`: `sha256:b5465173ecd3420e2cafee34e7542676379c20a4083db757f91682ee12f0e65f`;
- `claim`: `sha256:3205aa41139c82e2024c7f2feae5bea7c4c20f09073a526c43ea7297fe8b1231`.

## Triage

Tier 1 conjecture of a 2025 paper, preregistered in issue #16523 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the lower bound is a dimension count, linearity and the triangle inequality, and the attainment is a finite normalization of the source's strategy | open-problem-resolution |
| the dependence, readout, maximum, L¹ and explicit-strategy helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other declaration is a definition used by a public statement or a compiler-generated proof on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`: the public result is a universal lower bound together with its attainment, and the explicit strategy is used only inside that proof. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** every rebit strategy for the task has average trace distance at least 1/12 from the target, and the source's strategy attains it.

**Computed, not formalized** (orchestrator, NumPy, 14 October 2026):
- 300 random restarts of Nelder–Mead followed by Powell over all rebit strategies reach d = 0.083517, never below 1/12;
- the same optimizer over complex qubit strategies reaches d = 1.4 × 10⁻⁵, in agreement with the source's perfect complex-qubit strategy.

**Argued, not formalized.**
- The bound uses only that the four states lie in a three-dimensional real space and that the measurement is linear. It therefore holds for every real measurement, and indeed for every linear readout of the states, whatever Bob does.
- The argument generalizes. Take n inputs, the target P(y|x) = (1 − δ_xy)/(n − 1), and states in a real space of dimension less than n; for example, n > d(d + 1)/2 real d-level states. Then Σ_x w_x P(y|x) = −w_y/(n − 1), and the same estimate gives d ≥ 1/(n(n − 1)), which is 1/12 at n = 4. Whether this bound is attained for n > 4 is not examined.

- The no-shared-randomness assumption is essential. With a uniformly shared index over the partitions 01|23, 02|13 and 03|12:
  - Alice sends a real basis state naming the part that contains her input.
  - Bob outputs uniformly from the other part.
  - Distinct x, y are separated in two of the three partitions, so P(y|x) = (2/3)(1/2) = 1/3 and P(x|x) = 0. Hence d = 0 with real (indeed classical) messages.

  This construction was compiled in a review seat's scratch file; it is not formalized in the module.

**Open.**
- Whether 1/12 is the minimum for the source's other distances (for example the worst-case trace distance over inputs).

**Effect on the paper.** The weak conjecture of §IV and Appendix D is a theorem: the rebit minimum is exactly 1/12, so, without shared randomness or inter-round correlations, any realized distance below 1/12 certifies imaginarity in this task.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
