---
slug: vom-ende-shahbeigi-2024-stochastic-generator-set-refutation
bibkey: vomendeshahbeigi2024stochasticgenerators
doi: null
url: https://arxiv.org/abs/2411.18946v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.result
---

# The Eq. (10) set does not generate the 3 × 3 stochastic matrices

## Problem

F. vom Ende and F. Shahbeigi, *Generating Sets of Stochastic Matrices*, arXiv:2411.18946, study sets G of column-stochastic matrices whose finite products give every stochastic matrix. N_G(s(n)) is the number of factors needed in the worst case (Definition 3). These are the classical counterparts of generating sets of quantum channels: a generating set models the operations an experiment can implement, and N_G bounds the circuit length needed to implement every classical channel.

Theorem 3 states that G = {P} ∪ conv{1, V1, V2, V3} of Eq. (10) generates s(3) with G^20 = s(3). The Outlook asks "is the upper bound N_G(S) ≤ 20 in Theorem 3 optimal? We conjecture that this is true".

The verbatim statements are in [the literature note](../Library/QuantumChannels/vomendeshahbeigi2024stochasticgenerators.md).

Issue [#17954](https://github.com/the-omega-institute/trureturing/issues/17954) fixes the reading: N_G(s(3)) = 20, that is, G^20 = s(3) and G^19 ≠ s(3). This conjecture is refuted, together with the generation claim of Theorem 3.

## Motivation

The paper proposes Eq. (10) as an explicit, physically interpretable generating set for three-state classical channels, with a uniform bound on the number of elementary operations. The conjecture fixes that bound exactly at 20.

## Gap

Issue #17954 records the literature check before any Lean:
- arXiv v1 and v2 are the only versions ("submitted to Semigroup Forum"), and Crossref lists no journal version;
- OpenAlex lists no citing work;
- the repository had no record of the paper.

`not-found-in-searched-scope`.

## Route

Witness: A = [[1/4, 0, 1/4], [3/4, 1/2, 0], [0, 1/2, 3/4]], column-stochastic with a six-cycle support.
1. **Indivisibility.** If σAτ = BC for permutation matrices σ and τ and column-stochastic B and C, then B or C is a permutation matrix.
   - Each index k gives a rectangle, the support of column k of B times the support of row k of C, which lies in the support of σAτ.
   - A six-cycle contains no 2 × 2 rectangle, so three such rectangles can cover it only as three stars centred at all rows or at all columns.
2. **Reduction.** By induction on the number of factors, σAτ ∈ G^m forces σ′Aτ′ ∈ G for some permutation matrices σ′ and τ′.
3. **Exclusion.** No row and column permutation of A lies in G.
   - The swap has an entry equal to 1, while every entry of A, and hence of every permuted copy, is below 1.
   - The convex hull consists of the matrices [[a, 0, 1 − c], [1 − a, b, 0], [0, 1 − b, c]] with 1 ≥ a ≥ b ≥ c ≥ 0.
   - The permutations of A with that zero pattern have parameters (1/4, 1/2, 3/4), (1/2, 3/4, 1/4) or (3/4, 1/4, 1/2), none weakly decreasing.

Hence A ∉ G^20.

## Falsifier

The refutation would not settle the conjecture if:
- the formal G differed from Eq. (10);
- the products ran in the opposite order;
- the matrices were row- rather than column-stochastic.

The module takes:
- the swap of the first two levels, written with Mathlib's `permMatrix`;
- the three vertices of Eq. (10) entry by entry, and the convex hull in Mathlib's sense;
- products g · w of one generator and m − 1 earlier factors, so `genPow m` is the set G^m of Definition 3;
- Mathlib's `Matrix.colStochastic`, which is the column-stochastic convention of the source's s(3).

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.lean` (359 lines).
- It defines `V1`, `V2`, `V3`, `swap12`, `gen`, `genPow` and `claim`, and proves `result : ¬ claim`.
- It reuses Mathlib's column-stochastic matrices and permutation matrices, and the enumeration of the six permutations of three points from `ProjectionAMGMRefutation` (`sixPerms`, `sixPerms_univ`), made public by removing only `private`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registrations: `result` is the designated refutation result of the `utility` header and is exempt. The newly public `ProjectionAMGMRefutation.sixPerms_univ` is registered in `Reg/D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.lean`, `declared_validated`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/StochasticGeneratorSetRefutation.lean.json`, statement `sha256:e919930c8ef682fc30737ac1cdff75b3043c46e5de10c8e21001e9343c1dcec4`.

Declaration statements:
- `result`: `sha256:b67c170620f1e49af6e02b2e74054c43ce5d4192274e3bd9ca2f8075acfde5cb`;
- `claim`: `sha256:81b607678ed278da0f2835f0b394c4da1095bbef64fc9f3120cb6a6383e006ee`.

## Triage

Tier 1 conjecture of a 2024 paper, preregistered in issue #17954 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none: after inlining, the support argument is a finite case analysis and the exclusion is 36 rational comparisons | open-problem-resolution |
| the indivisibility, reduction and exclusion helpers (private) | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every other public declaration is a definition used by a public statement. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Refuted by `result`:** the matrix A is not a product of 20 elements of G. The proof shows more: A is not a product of any number of elements of G, so G does not generate s(3) and Theorem 3 fails.

**Argued, not formalized.**
- *Where the source's proof breaks.* The proof of Theorem 3 asserts that every matrix with a six-cycle support can be permuted into the ordered cell a ≥ b ≥ c. The six permutations that preserve the zero pattern act on (a, b, c) by cyclic shifts and by (a, b, c) ↦ (1 − a, 1 − c, 1 − b) and its cyclic variants. All of them preserve Δ = (a − b)(b − c)(c − a) (orchestrator, symbolic check of the six actions). The ordered cell has Δ ≤ 0, while Δ(A) = 1/32 > 0. Hence the indivisible matrices with Δ > 0 are never reached.
- *Restricting to positive matrices does not restore the bound.* G is compact, so G^20 is closed. Positive stochastic matrices are dense in s(3). If G^20 contained them all, it would contain A.

**Open.**
- Whether adding the reflected cell (a ≤ b ≤ c) to Eq. (10) gives a generating set, and the resulting N_G(s(3)).
- The second part of the source's question, the lower bound, which has no content for the set of Eq. (10) as it stands.

**Effect on the paper.** Theorem 3 and its bound N_G(s(3)) ≤ 20 do not hold for the set of Eq. (10). The set misses one of the two orientation classes of indivisible 3 × 3 stochastic matrices.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" and "Open" are not formalized.
