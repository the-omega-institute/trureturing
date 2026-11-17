---
bibkey: nathanson2025sumsetintersection
authors: Melvyn B. Nathanson
year: 2026
title: Intersections of sumsets in additive number theory
doi: 10.1017/S0004972726101270
url: https://arxiv.org/abs/2512.23574v3
claim: Problem 2 asks whether every nonmaximal nonbasis admits an asymptotically strictly decreasing approximation preserving its order-h sumset intersection.
strata_touched:
  - D5/S3/Arith/Additive/NathansonSumsetIntersectionNonmaximal
license: citation-only
triage: anchor
---

# Intersections of sumsets and nonmaximal nonbases

## Verified locator

DOI: 10.1017/S0004972726101270

Source: https://arxiv.org/abs/2512.23574v3

Published in *Bulletin of the Australian Mathematical Society* 114 (2026), 228–236.
Page numbers below refer to the arXiv v3 text.

## Source statements

Section 1, p. 1, states: “For every positive integer h, the h-fold sumset of A is the set of all sums of h not necessarily distinct elements of A, that is, hA = {a₁ + ⋯ + a_h : aᵢ ∈ A for all i = 1, …, h}.”

“The subset A is a basis of order h for S if hA = S, or, equivalently, if rA,h(x) ≥ 1 for all x ∈ S.”

“The sequence of sets (A_q)_{q=1}^∞ is decreasing if A_q ⊇ A_{q+1} for all q ∈ ℕ.”
“The decreasing sequence (A_q)_{q=1}^∞ is strictly decreasing if A_q ≠ A_{q+1} for all q ∈ ℕ and asymptotically strictly decreasing if A_q ≠ A_{q+1} for infinitely many q.”

Section 2, p. 5, states: “A subset A of S is a maximal nonbasis of order h for S if A is not a basis of order h for S but every proper superset of A is a basis of order h for S.”

Problem 2, p. 6, asks: “Let A be a subset of the infinite abelian semigroup S such that A is a nonbasis of order h but not a maximal nonbasis of order h for S. Does there exist an asymptotically strictly decreasing sequence (A_q)_{q=1}^∞ of subsets of S such that A = ⋂_{q=1}^∞ A_q and hA = ⋂_{q=1}^∞ hA_q? In particular, consider this problem for S = ℤ.”

## Encoding and scope

The Lean index starts at zero. Its positive-order sumset recursion agrees with the source's repeated pointwise addition; its unused zero-order value is empty. Semigroups need no additive identity. The assertion quantifies over infinite additive commutative semigroups and natural orders h with 1 ≤ h. The counterexample uses only ℤ, h = 2, and A = {n : ℤ | Even n ∧ n ≠ 2}.

## Supporting computation

The finite-window and residue checks are in `the-omega-institute/trureturing-experiments`, commit `941e62fe339291b2adfdf1720fa4b905f1666363`, at `docs/reports/nathanson-2025-sumset-intersection-nonmaximal/check.py`, SHA-256 `e90d02ac2cec489534c978c19f93f947f7353acae3d9c48ee1bd338112e36db5`. The recorded command `python3 docs/reports/nathanson-2025-sumset-intersection-nonmaximal/check.py` exits 0 with `ALL_CHECKS_OK`. These samples do not establish the universal refutation.

## Literature boundary

The screen recorded in [issue #20722](https://github.com/the-omega-institute/trureturing/issues/20722) includes the source versions and arXiv:2603.14510, 2603.15556 and 2604.04781. It found no direct settlement of this question. Exhaustive literature completeness remains `ASSUMED-UNVERIFIED`; the note makes no global novelty claim.
