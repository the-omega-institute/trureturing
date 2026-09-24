---
slug: hanna-shift-square-mod-eight
bibkey: hanna2026a392203
doi: null
url: https://oeis.org/A392203
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.result
---

# Hanna's Series A(x - A(x)) = x^2 + x A(x) Is Rational Modulo Eight

## Problem

OEIS A392203, by Paul D. Hanna, Jan 03 2026:

> G.f. A(x) satisfies A(x - A(x)) = x^2 + x*A(x).

The comment carrying the question:

> It appears that a(2*n) == 1 (mod 8) and a(2*n+1) == 3 (mod 8) for n >= 1.

## Motivation

The frozen theorem `D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.result` settles the comment for every
integer solution of order at least two, and shows that such a solution exists.

## Gap

Issue 9678 records the screen carried out before the work. The A-number appears nowhere under `Problems/`,
`D5/`, `Library/` or `Blueprint/`, nor in the screening records, nor in google-deepmind/formal-conjectures. The
entry records no proof and no reference; its cross-reference A276370 states no congruence for this sequence, and a
catalogue search by the terms returns only this entry. This is a bounded negative finding.

## Route

**One, contraction.** For a series `f` of order at least two put `T(f) = x^2 + x f - (f(x - f) - f)`; the equation is
`T(f) = f`. If `f` and `g` have order at least two and agree below degree `d`, then `T(f)` and `T(g)` agree below degree
`d + 1`: the difference `x(f - g)` gains a factor `x`; `f(x - f) - f(x - g)` is a sum of terms `c_k((x-f)^k - (x-g)^k)`
with `k ≥ 2`, each divisible by `(f - g)` times a series without constant term; and writing `f - g = x^d h`, the
difference `(f - g)(x - g) - (f - g) = x^d((1 - g/x)^d h(x - g) - h)` has no term of degree `d`.

**Two, existence.** Iterating `T` from zero over the integers, the `n`-th coefficient stabilises from the
`(n + 1)`-th iterate on; the series of stabilised coefficients is a fixed point of `T`.

**Three, uniqueness modulo eight.** Over `ZMod 8`, two fixed points of order at least two agree below every degree by
induction on step one, so they are equal.

**Four, the rational solution.** Let `S` be the series over `ZMod 8` with coefficient `0` below degree two, `1` at even
and `3` at odd degrees, so that `S(1 - x^2) = x^2 + 3x^3`. With `D = 1 - x^2` and `N = x - x^2 - 4x^3` one has
`(x - S) D = N`, and multiplying `S(x - S)(1 - (x - S)^2) = (x - S)^2 + 3(x - S)^3` by `D^3` turns the equation
`S(x - S) = x^2 + x S` into `N^2 D + 3 N^3 = (x^2 D + x^3 + 3x^4)(D^2 - N^2)`, a polynomial identity that holds modulo
eight because the two integer sides differ by a polynomial with every coefficient divisible by eight; `D` and
`D^2 - N^2` have constant term one and so are units. Hence `S` is a fixed point modulo eight.

**Five.** The reduction modulo eight of any integer solution is a fixed point there, hence equals `S` by step three,
and reading off coefficients gives the comment.

## Falsifier

The statement would fail if some even-index coefficient were not congruent to one, or some odd-index coefficient not
congruent to three, modulo eight. It does not extend to modulus sixteen: `a(6) = 1209` is congruent to `9`, not `1`,
modulo sixteen. Through degree sixty the even-index coefficients modulo sixteen take the values `1` and `9` and the
odd-index ones `3` and `11`, repeating with period six from degree four; that pattern is observed on the computed
prefix only and is not proved here.

## Evidence

Solving the equation coefficient by coefficient reproduces the entry's first eleven terms, and every coefficient up to
degree sixty satisfies the congruences. The polynomial identity of step four was checked symbolically: every
coefficient of the difference of its two integer sides is divisible by eight.

## Triage

`theorem`; Tier 1 named external open question from 2026, preregistered in issue 9678 before the work. The
computational use is `none`: the delivered statement quantifies over every solution and every index.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The entry was read in full and records no proof and no reference to one. Citation
indices, printed sources and the resolved set of arXiv:2608.11941 were not exhaustively compared, so no worldwide
priority claim is made.
