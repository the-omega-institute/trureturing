---
bibkey: pan2026permanental
authors: Sihong Pan, Mark Skandera, Jiayuan Wang
year: 2026
title: "Permanental Inequalities and Unit Interval Orders"
doi: 10.4204/EPTCS.445.17
url: https://arxiv.org/abs/2606.13162v1
claim: "Conjecture 7.8. For all n and all w ∈ A_n we have w ≤ f_n(w) in the Bruhat order."
strata_touched:
  - D5/S3/Combinatorics/PanSkanderaWangBruhat
license: citation-only
triage: anchor
---

# Pan, Skandera and Wang, permanental inequalities and a Bruhat-increasing bijection

The paper studies inequalities between products of permanents of complementary submatrices of
totally nonnegative matrices. For the split at `h = ⌊n/2⌋` it reduces the inequality for all totally
nonnegative matrices to the existence of a bijection `f_n : A_n → B_n` with `w ≤ f_n(w)` in the
Bruhat order, and constructs a candidate `f_n` recursively.

## Verified locator

DOI: 10.4204/EPTCS.445.17

URL: https://arxiv.org/abs/2606.13162v1

The arXiv record shows only v1 (11 June 2026); the paper appears in EPTCS 445 (2026), pp. 139–147.

- Locator: (7.3), `A_n = {w ∈ S_n | w_1 ⋯ w_t permutes {1,…,t} and w_{t+1} ⋯ w_n permutes {t+1,…,n}}`,
  `t = ⌊n/2⌋`; (7.4), `Ã_n` is the same with `t + 1` in place of `t`.
- Locator: the maps `ins_p : S_n → S_{n+1}`, `w ↦ w_1 ⋯ w_{p−1}(n+1)w_p ⋯ w_n`, and
  `inss_q : S_n → S_{n+1}`, `w ↦ w_1 ⋯ w_{q−1}(n+1)w_{q+1}w_q w_{q+3}w_{q+2} ⋯ w_n w_{n−1}`
  (defined when `n + 1 − q` is even), and the reverse-complement `U ∘ R`.
- Locator: (7.6), `f̃_n(w̃) = [f_n(w̃^{RU})]^{RU}`; Algorithm 7.5, starting from
  `f_4 : 1234 ↦ 1234, 1243 ↦ 1432, 2134 ↦ 3214, 2143 ↦ 3412` and, for odd `n = 2k + 1`,
  `f_n(w) = inss_{2(p−k)−1}(f_{n−1}(a))` where `w = ins_p(a)`; for even `n = 2k + 2`,
  `f_n(u) = inss_{2(q−k−1)}(f̃_{n−1}(w̃))` where `u = ins_q(w̃)`.
- Locator: Theorem 7.7, "For n ≤ 13 and all w ∈ A_n, we have w ≤ f_n(w) in the Bruhat order.
  Proof omitted."
- Locator: Conjecture 7.8, "For all n and all w ∈ A_n we have w ≤ f_n(w) in the Bruhat order.
  A proof of Conjecture 7.8 would extend Theorem 5.1 to all totally nonnegative matrices."

## Reading of the statement

Permutations are words in one-line notation. The Bruhat order is the strong Bruhat order of the
symmetric group; by the tableau criterion (Björner and Brenti, *Combinatorics of Coxeter Groups*,
Theorem 2.1.5) `x ≤ y` exactly when `#{j ≤ p : x_j ≥ q} ≤ #{j ≤ p : y_j ≥ q}` for all `p, q`.
The algorithm defines `f_n` for every `n ≥ 4`, so "for all n" means every `n ≥ 4`.

## Scope of the recorded answer

The conjecture holds for every `n ≥ 4`. The proof carries a stronger selection invariant through
the recursion: for the positions `S(p, d) = [p − d] ∪ {p − d + 2, p − d + 4, …, p + d}` the count of
entries `≥ q` of `w` among its first `p` positions is at most the count of entries `≥ q` of `f_n(w)`
on `S(p, d)`, for every admissible `d`. The case `d = 0` is the Bruhat comparison. The invariant is
preserved by the reverse-complement conjugation and by the paired insertions `ins_r`, `inss_{2r−n}`.

## Bounded prior-resolution evidence

Read on 2026-09-24: the arXiv record (v1 only), the EPTCS volume page, google-deepmind
formal-conjectures, conjectures.io and the mathdb entry for the conjecture, which lists it as open
without solution; searches by title, arXiv number and "Conjecture 7.8" returned no later proof.
Citation indices were not exhaustively reachable, so this is a bounded negative finding.
