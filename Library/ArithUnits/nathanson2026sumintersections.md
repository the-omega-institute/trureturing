---
bibkey: nathanson2026sumintersections
authors: Melvyn B. Nathanson
year: 2026
title: Problems and results on intersections of product sets and sumsets in semigroups
doi: 10.48550/arXiv.2604.04781
url: https://arxiv.org/abs/2604.04781v2
claim: Problem 9 asks for a nontrivial proper product intersection spectrum in every infinite torsion group; Problem 12 asks for affine invariance of integer sum intersection spectra.
strata_touched:
  - D5/S3/Arith/Additive/NathansonProblem12AffineInvariance
  - D5/S3/Combinatorics/GroupWords/NathansonProblem9
license: citation-only
triage: anchor
---

# Sum intersection sets and affine transformations

## Verified locator

DOI: 10.48550/arXiv.2604.04781

Source: https://arxiv.org/abs/2604.04781v2

## Source statements

Section 1, p. 1, defines “the h-fold sumset hA = {a₁ + a₂ + ⋯ + a_h : a_i ∈ A for all i = 1, …, h}”.
It states on p. 2: “For an additive semigroup S and index set Q, we define the sum intersection set”
H(A_q) = {h ∈ ℕ : hA = ⋂_{q∈Q} hA_q}, with A = ⋂_{q∈Q} A_q and ℕ = {1, 2, 3, …}.

Section 2, p. 3, states: “A sequence (A_q) of subsets of a set S is decreasing if A_q ⊇ A_{q+1} for all q ∈ ℕ … A decreasing sequence (A_q) is asymptotically strictly decreasing if A_q ≠ A_{q+1} for infinitely many q ∈ ℕ.”

Problem 12, p. 21, asks verbatim: “Let (A_q) and (A′_q) be asymptotically strictly decreasing sequences of sets of integers such that A′_q = sA_q + t for all q ∈ ℕ and some s, t ∈ ℤ with s ∉ {0, ±1}. Does this imply H(A_q) = H(A′_q)?”

Theorem 15, pp. 20–21, treats the unit case using the relation
“A′ = εA + t = {εa + t : a ∈ A}”.

## Mathematical scope

The Lean index type ℕ+ represents the paper's positive integers. Sum lengths
are natural numbers restricted by 0 < h. The expression h • B is the pointwise
h-fold sumset. The affine expression sA + t is the image of A under a ↦ sa + t.

The repository's affirmative answer uses injectivity, image transport through
nonempty indexed intersections, and h(sB + t) = s(hB) + ht. The proof requires
only s ≠ 0 and uses neither decrease premise. The source's statements remain
unchanged; its unit case and the other questions retain their stated scope.

## Literature boundary

The preregistration at https://github.com/the-omega-institute/trureturing/issues/18994
records a screen of arXiv:2604.18869v2, whose advertised resolutions concern
Problems 10, 11 and parts of 4 and 7. Exhaustive literature completeness is
ASSUMED-UNVERIFIED; this note makes no global novelty claim.

## Product intersection spectra in groups

Problem 9, Section 4, asks: “Let G be an infinite torsion group. Describe the product intersection sets H_Q(G). Must there exist X in H_N^*(G) with X != {1} and X != N?”
Here N denotes the positive integers, B^h consists of ordered products with repetitions, and
H_N^*(G) consists of spectra of asymptotically strictly decreasing sequences of subsets of G.
Empty common intersections are permitted.

`D5/S3/Combinatorics/GroupWords/NathansonProblem9.result` answers the final existence question
for every infinite group, with arbitrary cardinality. Its cube-range dichotomy produces a
strictly decreasing family with empty core. Finite cube range gives 2 in the spectrum and
3 outside; infinite cube range gives 3 in the spectrum and 2 outside. The statement concerns
the full positive spectrum, rather than a spectrum truncated to those two exponents.
The preceding spectrum classification request remains outside this conclusion.

## Ramsey supplier and license

The proof consumes Yann Pequignot's *lean-infinite-ramsey*, revision
`b63066fd9f8075a30bc78d392405426bf084e226`:

- Source: https://github.com/yannpequignot/lean-infinite-ramsey/blob/b63066fd9f8075a30bc78d392405426bf084e226/InfiniteRamsey.lean
- Original source SHA-256: `12958fb0da027fc71a2aa5a2a1bd2a048eb1bee290e934c510e3f95ac31be4ad`.
- Consumed declarations: `infinite_ramsey`, `exists_infinite_fiber_nat` and `Set.Infinite.exists_strictMono`, with the private `RamseyState` construction used by the first.
- Full Apache-2.0 license: `docs/reports/licenses/lean-infinite-ramsey-LICENSE.txt`, SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
- The pinned recursive source tree contains no NOTICE file. The source copyright and author notice are preserved with the port.

The supplier pins Lean `v4.28.0` and Mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`; this repository pins Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. These pins prevent a common dependency resolution,
so the consumed source uses the compatible-port form. Its proof bodies are preserved;
the import `Mathlib.Data.Nat.Lattice` becomes `Mathlib.Order.Lattice.Nat`, and the deprecated
`Set.Infinite.diff` and `Set.diff_subset` names become their `sdiff` counterparts.
Explicit imports and private visibility adapt the source to its consumer. The unused
`infinite_ramsey_seq` corollary is omitted. The port's change notice records these changes.
Retire it when this repository's own pinned Mathlib contains an equivalent relativized,
all-arity finite-colour infinite Ramsey theorem, and directly apply that theorem instead.

The primary Nathanson HTML displays [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
This note quotes its question and definitions with attribution and mathematical notation
rendered in plain text, and cites the original; it does not redistribute the complete article.
The Ramsey code carries its independent Apache-2.0 license, rather than inheriting the
citation-only classification of this bibliography entry.

## Problem 9 literature boundary

The preregistration at https://github.com/the-omega-institute/trureturing/issues/21237#issuecomment-6390094250
fixes only the final existence question. The bounded repository and pinned-library search
found no exact group-existence result; the existing Problem 12 theorem is about integer-additive
affine transport. The source screen distinguishes van Doorn–Monticone–Tang,
arXiv:2604.18869v2, whose advertised resolutions concern Problems 10, 11 and parts of 4 and 7.
Absence of every prior solution remains ASSUMED-UNVERIFIED. The stronger all-infinite-group
scope contributes no additional externally named unit or global priority claim.
