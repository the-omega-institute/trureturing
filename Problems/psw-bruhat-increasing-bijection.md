---
slug: psw-bruhat-increasing-bijection
bibkey: pan2026permanental
doi: 10.4204/EPTCS.445.17
url: https://arxiv.org/abs/2606.13162v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PanSkanderaWangBruhat.result
---

# The Pan–Skandera–Wang Map Is Bruhat-Increasing for Every n

## Problem

Sihong Pan, Mark Skandera and Jiayuan Wang, *Permanental Inequalities and Unit Interval Orders*,
EPTCS 445 (2026), arXiv:2606.13162v1, Section 7:

> Conjecture 7.8. For all n and all w ∈ A_n we have w ≤ f_n(w) in the Bruhat order.
> A proof of Conjecture 7.8 would extend Theorem 5.1 to all totally nonnegative matrices.

Here `A_n` is the set of permutations whose first `⌊n/2⌋` entries permute `{1, …, ⌊n/2⌋}`, and
`f_n` is defined by Algorithm 7.5 from `f_4` through the insertion maps `ins_p`, `inss_q` and the
reverse-complement conjugation. Theorem 7.7 of the paper states the case `n ≤ 13`, with proof omitted.

## Motivation

The frozen theorem `D5/S3/Combinatorics/PanSkanderaWangBruhat.result` proves the conjecture for every
`n ≥ 4`, the range on which Algorithm 7.5 defines `f_n`. By Theorem 7.1 of the paper (Drake, Gerrish,
Skandera), each comparison `w ≤ f_n(w)` makes the corresponding difference of monomials totally
nonnegative, so the bijection gives the permanental inequality at `h = ⌊n/2⌋` for all totally
nonnegative matrices.

## Gap

Issue 9706 records the screen made before the work. The arXiv record has only v1; the mathdb entry
lists the conjecture as open without solution; google-deepmind/formal-conjectures and conjectures.io
have no entry; searches by title, arXiv number and conjecture number found no later proof. Nothing
under `Problems/`, `D5/` or `Library/`, and no entry of the three screening records, concerns this
paper. Mathlib has no Bruhat order on permutations, so the formal statement uses the tableau
criterion of Björner and Brenti, Theorem 2.1.5.

## Route

Write `R_x(p, q) = #{j ≤ p : x_j ≥ q}` and, for `0 ≤ d ≤ min(p, n − p)`,
`S(p, d) = [p − d] ∪ {p − d + 2, p − d + 4, …, p + d}`, a set of `p` positions. The invariant (F)
for a pair `(x, y)` says `R_x(p, q) ≤ #{j ∈ S(p, d) : y_j ≥ q}` for all `p, d, q`; its case `d = 0`
is Bruhat domination. For `w ∈ A_n` let `r` be the position of `n`; in both parity branches of
Algorithm 7.5 the insertion position of the output is `s = 2r − n`.

1. The base map `f_4` satisfies (F) on its four inputs.
2. Reverse-complement conjugation preserves (F): the complement of the reflected selection
   `S(p, d)` is `S(n − p, d)`, and `R_{x^{RU}}(p, q) = p − q + 1 + R_x(n − p, n + 2 − q)`.
3. If `(a, b)` satisfies (F) and `s = 2r − n`, then `(ins_r(a), inss_s(b))` satisfies (F). The proof
   compares the selected positions of the new word with those of the old one in six cases, by the
   position of `s` relative to `p − d` and `p + d` and by parity; only the last case uses
   `s = 2r − n`.
4. Deleting the maximum of `w ∈ A_n` gives an element of `A_{n−1}` for odd `n` and of `Ã_{n−1}` for
   even `n`; reverse-complementation maps `Ã_{n−1}` into `A_{n−1}`.

Induction on `n` gives (F) for every pair `(w, f_n(w))`, hence `w ≤ f_n(w)`.

## Falsifier

The statement would fail if some `w ∈ A_n` had `R_w(p, q) > R_{f_n(w)}(p, q)` for some `p, q`. It
would fail to be the paper's statement if the insertion positions `2(p − k) − 1` and `2(q − k − 1)`
were read with a different `k`, or if the Bruhat order were replaced by a weaker order; the formal
module transcribes Algorithm 7.5 literally, and its map was checked against an independent
implementation on all of `A_n` for `n ≤ 9`.

## Evidence

Exhaustive checks of (F), its reverse-complement pairs, and every row of the insertion case table
through `n = 13` (4,251,652 source words), with an independent implementation agreeing through
`n = 9`. The six-row insertion table was also checked by hand.

## Triage

`theorem`; Tier 1 named open conjecture from a 2026 paper, preregistered in issue 9706 before the
work. The computational use is `none`: the delivered statement is universally quantified over every
`n ≥ 4`, and no declaration is a bounded enumeration, a checker, a numeric reduction or a certified
instance.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; citation indices were not exhaustively
reachable, so no worldwide priority claim is made. The equivalence between the tableau criterion
and the strong Bruhat order is taken from the literature and is not formalized here. The result
settles Conjecture 7.8 at `h = ⌊n/2⌋`; the paper's further conjecture for all `h` is not addressed.
