---
slug: sa-ribeiro-prosen-bernard-2024-steady-state-block-refutation
bibkey: saribeiroprosenbernard2024symmetryclasses
doi: 10.1007/s10955-025-03423-y
url: https://arxiv.org/abs/2406.17955v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.result
---

# The steady-state block of a Markov generator with a commuting symmetry need not admit a Markov form

## Problem

L. Sá, P. Ribeiro, T. Prosen and D. Bernard, *Symmetry Classes of Classical Stochastic Processes*, J. Stat. Phys. 192, 41 (2025), arXiv:2406.17955, classify the symmetries of Markov generators L, real matrices with nonnegative off-diagonal rates and zero column sums (Eqs. (2)–(4)).

A commuting symmetry U splits L into blocks, and the classification applies to each irreducible block that is itself a Markov generator. The authors write after Eq. (5): "It is, however, natural to conjecture that the block containing the invariant measure of the Markov process (henceforth referred to as the steady-state block) can still be recast into Markov form." Appendix A proves this under the extra assumption (A3).

The verbatim statements are in [the literature note](../Library/StatisticalMechanics/saribeiroprosenbernard2024symmetryclasses.md).

Issue [#17999](https://github.com/the-omega-institute/trureturing/issues/17999) fixes the reading. Take a Markov generator L, a commuting real orthogonal U, and a stationary probability p. Let the steady-state block be a whole eigenspace of U that contains p, with no further unitary symmetry. Then the restriction of L to it is similar to a Markov generator. This conjecture is refuted.

## Motivation

The classification of the source assumes either no commuting symmetry or a restriction to the steady-state block, read as a Markov generator in its own right. The conjecture would make the classification apply to every Markov process with a commuting symmetry.

## Gap

Issue #17999 records the literature check before any Lean:
- arXiv v1 and v2 and the journal version keep the conjecture;
- OpenAlex lists three citing works, which do not settle it (search seat);
- arXiv searches for the steady-state block find no settlement;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

1. **Witness.** The four-state generator L = (1/256)[[−295, 25, 25, 281], [273, −303, 17, 17], [7, 263, −313, 7], [15, 15, 271, −305]].
   - Every off-diagonal rate is at least 7/256, so all rates are positive.
   - Its unique stationary probability is p = (1/64)(17, 17, 15, 15).
2. **The symmetry and the block.** U = 1 − vvᵀ/2 with v = (1, −1, 1, −1) is a real orthogonal involution commuting with L, and Up = p.
   - Its +1 eigenspace v⊥ has dimension 3 and contains p.
   - In an orthonormal basis of v⊥, L restricts to A = [[0, 0, 0], [5/64, −5/4, −1], [−1/16, 1, −5/4]].
3. **Irreducibility.** A unitary X commuting with A also commutes with Aᵀ.
   - ker Aᵀ is spanned by e₀, so X fixes the line of e₀.
   - e₀, Ae₀ and A²e₀ form a basis (determinant 41/4096), so X is a scalar.
4. **No Markov form.** For every real 3 × 3 matrix B with nonnegative off-diagonal entries, 3 tr(B²) − (tr B)² = Σ_{i<j}(B_ii − B_jj)² + 6(B₀₁B₁₀ + B₀₂B₂₀ + B₁₂B₂₁) ≥ 0.
   - Similarity preserves both traces.
   - For A the value is 3 · 9/8 − 25/4 = −23/8 < 0.

## Falsifier

The refutation would not settle the conjecture if:
- the module's notion of a Markov generator differed from Eqs. (2)–(4);
- its block were not an irreducible block containing the invariant measure;
- "recast into Markov form" allowed more than a change of basis.

The module's `claim` keeps every hypothesis of the source:
- the generator, the commuting orthogonal symmetry and the stationary probability;
- the block as a whole eigenspace of U, orthonormally spanned, invariant under L and containing p;
- irreducibility under every complex unitary commuting with the restriction.

It asks only for similarity by an invertible complex matrix to a real Markov generator.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.lean` (229 lines).
- It defines `IsMarkovGenerator` and `claim`, and proves `result : ¬ claim`.
- It reuses `Probability` of `CycleSingleCutMinimax` and Mathlib's orthogonal and unitary groups.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration: `result` is the designated refutation result of the `utility` header and is exempt; the module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/SteadyStateBlockMarkovFormRefutation.lean.json`, statement `sha256:aea22c6a54170a2fae00affc0444e04f5527eb3867bac902e0e05dd5697a297b`.

Declaration statements:
- `result`: `sha256:b0b4a261d07099ffd804216cc10ad4534871bd18c36c4c6a0c1e916388bb6f46`;
- `claim`: `sha256:03ec4046ea43547289e4ef7a779946511848e8584e75aaaed9ebfd5796eef102`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #17999 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the witness checks are rational identities, irreducibility is a finite linear-algebra computation, and the obstruction is a sum-of-squares identity with trace invariance | open-problem-resolution |
| the witness, irreducibility and trace helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** the irreducible steady-state block of the four-state generator above is similar to no Markov generator.

**Computed, not formalized** (orchestrator, SymPy, recorded in #17999):
- the spectrum of the block is 0 and −5/4 ± i, and the complementary eigenvalue is −9/4;
- ker L is one-dimensional, so p is the unique stationary probability.

**Argued, not formalized.**
- *Mechanism.* The block v⊥ meets the nonnegative orthant in a cone with four extreme rays, e₀ + e₁, e₀ + e₃, e₂ + e₁ and e₂ + e₃. The block dynamics preserves that cone, and so maps probability vectors to probability vectors, as the source argues. A Markov form in dimension 3 would give an invariant simplicial cone, the image of the nonnegative orthant under the change of basis. The trace obstruction excludes every such cone, since it excludes every matrix with nonnegative off-diagonal entries.
- *Where the source's sufficient condition fails.* The block projector 1 − vvᵀ/4 has negative entries, so no basis of the block consists of nonnegative vectors with conditional probabilities in {0, 1}, as assumption (A3) requires.

**Open.**
- Which commuting symmetries guarantee a Markov form for the steady-state block, beyond assumption (A3).
- Whether the block always admits a Markov form after allowing more states, through a positive realization on the extreme rays of its invariant cone, and how the symmetry classes of the source behave under such a realization.

**Effect on the paper.** The classification applies to the steady-state block only when that block is itself a Markov generator, for example under (A3). It does not apply to every Markov process with a commuting symmetry.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Computed, not formalized", "Argued, not formalized" and "Open" are not formalized.
