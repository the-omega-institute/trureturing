---
bibkey: nathanson2026sumintersections
authors: Melvyn B. Nathanson
year: 2026
title: Problems and results on intersections of product sets and sumsets in semigroups
doi: 10.48550/arXiv.2604.04781
url: https://arxiv.org/abs/2604.04781v2
claim: Problem 12 asks whether non-unit affine transformations of integer-set sequences preserve their sum intersection sets.
strata_touched:
  - D5/S3/Arith/Additive/NathansonProblem12AffineInvariance
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
