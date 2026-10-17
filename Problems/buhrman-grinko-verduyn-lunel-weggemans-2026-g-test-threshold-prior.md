---
slug: buhrman-grinko-verduyn-lunel-weggemans-2026-g-test-threshold-prior
bibkey: buhrmangrinkoverduynlunelweggemans2026permutation
doi: null
url: https://arxiv.org/abs/2405.09626v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/GTestThresholdPrior.result
---

# The threshold prior of the G-test is O/(M + O)

## Problem

H. Buhrman, D. Grinko, P. Verduyn Lunel and J. Weggemans, *Permutation tests for quantum state identity*, arXiv:2405.09626v2, distinguish the twirled unequal-case state ρ̃^µ_≠ (Eqs. (11)–(12)) from the equal-case state ρ^n_= (Eq. (13)).
- **The G-test.** For a subgroup G of S_n, the G-test measures Π_= = Π_G = (1/|G|) Σ_{π∈G} ψ(π) (Eqs. (61)–(62)). Its completeness is 1 (Eq. (63)).
- **The Bayesian comparison.** With prior {p, 1 − p}, the success probability is P_succ = p P_c + (1 − p) P_s. The trivial test always answers "not equal" and succeeds with probability 1 − p. For G = S_n, Theorem 5 gives the threshold p∗(µ) = 1/(1 + (n choose µ)).
- **The question.** §6: "A further open question is to determine, for a given subgroup G and partition µ, the threshold prior p∗(G, µ) below which the trivial test outperforms the G-test, analogous to the threshold p∗(µ) established for the permutation test in Theorem 5."

The verbatim statements are in [the literature note](../Library/QuantumBounds/buhrmangrinkoverduynlunelweggemans2026permutation.md).

Issue [#17307](https://github.com/the-omega-institute/trureturing/issues/17307) fixes the reading:
- W_µ is the set of words of length n over {1, …, d} with µ_i letters i, of size M = n!/∏_i µ_i!;
- O is the number of orbits of G on W_µ.

The answer is p∗(G, µ) = O/(M + O):
- the G-test has strictly larger success probability than the trivial test exactly when p > O/(M + O);
- the two probabilities are equal exactly when p = O/(M + O);
- the soundness error is Tr[Π_G ρ̃^µ_≠] = O/M.

## Motivation

The permutation test (G = S_n) is optimal among tests that use the symmetry of the problem, and Theorem 5 locates the prior below which no test beats the trivial one. Subgroup tests are cheaper to implement; the threshold tells when such a test is still worth running.

## Gap

Issue #17307 records the literature check before any Lean:
- arXiv v2 (April 2026) states the open question in §6;
- the citing works arXiv:2610.04597 and arXiv:2606.20238, read in full, cite the paper only as a reference;
- no settlement was found on Zenodo, Crossref or in the repository Naixu-Guo/quantum-open-problems;
- the repository had no entry for the paper.

`not-found-in-searched-scope`.

## Route

1. **The diagonal of Π_G.** For a word w, ⟨w|Π_G|w⟩ = |Stab_G(w)|/|G|, since ψ(π)|w⟩ = |π·w⟩.
2. **Independence of U.** Π_G commutes with U^{⊗n}, so Tr[Π_G ρ̃] is the same for every unitary U, hence equal to its Haar average.
3. **The orbit average.** Averaging over S_n spreads |w⟩⟨w| uniformly over its orbit W_µ (orbit–stabilizer), so Tr[Π_G ρ̃] = (1/M) Σ_{x∈W_µ} |Stab_G(x)|/|G|.
4. **Burnside.** Σ_{x∈W_µ} |Stab_G(x)| = |G| · O, so Tr[Π_G ρ̃] = O/M.
5. **Completeness.** ψ(π) fixes |φ⟩^{⊗n}, so the completeness is 1.
6. **The comparison.** P_succ(G) − P_succ(trivial) = p + (1 − p)(1 − O/M) − (1 − p) = ((M + O)p − O)/M.

## Falsifier

The theorem would not answer the question if:
- the module's G-test differed from Π_G of Eq. (62);
- its unequal-case state differed from ρ̃^µ_≠ beyond replacing the Haar integral by a fixed U, which does not change the tested trace;
- its trivial test or Bayesian success probabilities differed from §4.1;
- the threshold were stated only one-sidedly.

The module quantifies over every n, d, subgroup G, word w with two distinct letters, unitary U, unit vector φ and p ∈ [0, 1], and states both the strict comparison and the equality case together with the soundness trace.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/GTestThresholdPrior.lean` (450 lines, `generality: G`, `utility: none`).
- It defines `TensorVec`, `TensorMat`, `WordOrbit`, `orbitMap`, `M`, `O`, `psi`, `ket`, `tensorPower`, `repeatKet`, `equalState`, `PiG`, `rhoTilde`, `completeness`, `soundnessError`, `soundness`, `P_G`, `P_T` and `claim`, and proves `result : claim`.
- The definitions reuse frozen D5 and Mathlib objects:
  - `ProductPrefixRigidity.productMap` for U^{⊗n} and |φ⟩^{⊗n};
  - `PureStateHandshake.rankOneDensity`;
  - `OccupancyWordSectors.Word`;
  - `RHLinalg.rtrace`;
  - `UnifiedPinchingFee.doorGap` for 1 − r;
  - Mathlib `Matrix.permMatrixHom`, `Finset.expect` and `AffineMap.lineMap`.
- The proof uses Mathlib's Burnside lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` and the frozen `ExactConditionalPreparationCost.hsandwich`. It also uses two lemmas made public for this settlement:
  - `TwoPositiveTransitionTrace.trace_rank_one`;
  - `NonlocalityDepthQuantumBound.Tensor.tensor_star`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations:
  - `Reg/D5/S3/Quantum/Measurements/GTestThresholdPrior.lean` reads out the soundness trace Tr[Π_G ρ̃] of `claim`, and is `declared_validated`. Its rejected realization, the trace plus 1, fails at n = d = 2, G = S_2 and the word (1, 2).
  - `trace_rank_one` and `tensor_star` are registered in `Reg/D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace.lean` and `Reg/D5/S3/QuantumBounds/NonlocalityDepthQuantumBound.lean`. Both registrations are `declared_unresolved`, with the judge reading `IE-C050 … reason=unclassified_form`. Their escape audit is incomplete; the template gap is recorded in [#16937](https://github.com/the-omega-institute/trureturing/issues/16937).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/GTestThresholdPrior.lean.json`, statement `sha256:9d1c238e21d06151389d9b04640124bdd7ffa15ef38f3e5c00bfa5b784abb67e`.

Declaration statements:
- `result`: `sha256:aa0aa68092c6f75cd783621b071ddd961ad37aeb27b396922faddb869f067f2b`;
- `claim`: `sha256:a97f08e36c1e84c5c7b879c7abfc520d1b747cfb506b514281fa1cb0090b602d`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the diagonal of Π_G, the orbit average, Burnside's lemma and the comparison are instantiations of frozen D5 and pinned Mathlib results followed by normalization | open-problem-resolution |
| the permutation, tensor, trace, orbit and comparison helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The module's 27 private theorems are bind-only helpers consumed on the proof path of `result`, and its one private definition and its compiler-generated declarations also lie on the proof path of `result`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The utility is `none`. There is no digestion atom.

## Triage

### What the settlement shows

**Proved by `result`:** for every subgroup G ≤ S_n and every word type µ with µ_2 > 0, the G-test beats the trivial test exactly when p > O/(M + O), ties exactly at p = O/(M + O), and has soundness error O/M. For G = S_n there is one orbit, so p∗ = 1/(M + 1), which is Theorem 5.

**Computed, not formalized** (orchestrator, NumPy with exact fractions, 15 October 2026; recorded in #17307): for n = 3, 4, 5, d = 2, 3 and G ∈ {trivial, S_n, C_n, Klein four-group}, the average of ⟨π·w|Π_G|π·w⟩ over π ∈ S_n equals O/M in all 18 cases.

**Argued, not formalized.**
- Since 1 ≤ O ≤ M, the threshold lies in [1/(M + 1), 1/2]. It equals 1/(M + 1) exactly when G acts transitively on W_µ, and 1/2 exactly when G fixes every word of W_µ, for example G trivial, where Π_G = 1 and the G-test always answers "equal".
- If G ≤ H, every H-orbit is a union of G-orbits, so O_H ≤ O_G and p∗(H, µ) ≤ p∗(G, µ): a larger symmetry group never raises the threshold.
- Comparing with Eq. (65) gives Σ_λ K_{λ,µ} r^G_λ = O, the number of G-orbits on W_µ. This is the multiplicity of the trivial representation of G in the permutation module on W_µ, decomposed by Young's rule.

**Open.**
- The other questions of §6 are not addressed.

**Effect on the paper.** The threshold prior of §6 is O/(M + O) for every subgroup G, with O the number of G-orbits on the words of type µ. The soundness of Eq. (65) can be computed by counting orbits instead of irreducible representations.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized" and "Argued, not formalized" are not formalized.
