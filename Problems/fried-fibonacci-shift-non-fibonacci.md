---
slug: fried-fibonacci-shift-non-fibonacci
bibkey: fried2025proofs
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result
---

# Fried's Fibonacci Shift Conjecture

## Problem

Fried, *Journal of Integer Sequences* **28** (2025), Article 25.4.3, Section 6,
states:

> Nevertheless, we were not able to show that the two sets
> `{ nF(n/2 + 3) − (n − 1)F(n/2 + 2) : n ≥ 1 is even }`,
> `{ F((n+1)/2 + 2) : n ≥ 1 is odd }`
> are disjoint, or, equivalently, that for every `n ∈ N`, the number
> `F(n + 2) + 2nF(n + 1)` is not a Fibonacci number. We conjecture that this is
> so.

Here `F(1) = F(2) = 1`. Both sets are indexed by `n ≥ 1`, so the `N` of the
equivalent form starts at one; `n = 0` gives `F(2) = 1`, which is a Fibonacci
number, and is outside the range.

## Motivation

The frozen theorem `D5/S3/Arith/FriedFibonacciShiftNonFibonacci.result` settles
the conjecture affirmatively in the equivalent form the source itself supplies:
for every `n` at least one and every index `m`, `F(m)` differs from
`F(n + 2) + 2nF(n + 1)`.

## Gap

The source reaches the conjecture from the closed-form description of A248982 and
offers no line of attack, writing only that a proof "likely proceeds along
similar lines as the previous theorem" — the previous theorem being a
rounding-formula induction with no Fibonacci content. The obstacle is that
`F(n + 2) + 2nF(n + 1)` grows like `2n` times a Fibonacci number, so it is not
close to any single Fibonacci number in ratio, and the usual identities for
`F(a) ± F(b)` do not apply. The recorded proof works instead with the exact
position of the number between two consecutive Fibonacci numbers of shifted
index.

## Route

Write `X n = F(n + 2) + 2nF(n + 1)`. The recurrence gives
`X n = F(n) + (2n + 1)F(n + 1)`.

Suppose `F(m) = X n` for some `n ≥ 1`.

Small `n`. For `n ≤ 7` the values of `X n` are `4, 11, 23, 48, 93, 177, 328`, all
below `F(14) = 377`. Since `F` is monotone, `m < 14`, leaving finitely many pairs
`(n, m)`, none of which is a solution.

Large `n`. For `n ≥ 8` first note `X n ≥ 3F(n + 1) > F(n + 1)`, so `m ≥ n + 2`;
write `m = j + n + 1` with `j ≥ 1`. The addition formula
`F(j + n + 1) = F(j)F(n) + F(j + 1)F(n + 1)` turns `F(m) = X n` into

    F(j)F(n) + F(j + 1)F(n + 1) = F(n) + (2n + 1)F(n + 1).

Since `F(j) ≥ 1`, the left side is at least `F(n) + F(j + 1)F(n + 1)`, so
`F(j + 1) ≤ 2n + 1` and the equation rearranges, with subtraction staying inside
the natural numbers, to

    (F(j) − 1)F(n) = (2n + 1 − F(j + 1))F(n + 1).

If `F(j) = 1` then `j ≤ 2`, so `F(j + 1) ≤ 2` while the right factor `2n + 1` is
at least seventeen; comparing the two sides of the original equation after
cancelling `F(n)` gives `F(j + 1)F(n + 1) = (2n + 1)F(n + 1)` with
`F(j + 1) ≤ 2 < 3 ≤ 2n + 1`, which is impossible because `F(n + 1) > 0`.

Otherwise `F(j) ≥ 2`, so `F(j) − 1 > 0`. The displayed identity shows that
`F(n + 1)` divides `(F(j) − 1)F(n)`, and `F(n)` and `F(n + 1)` are coprime, so
`F(n + 1)` divides `F(j) − 1` and hence `F(n + 1) ≤ F(j) − 1`. The left side of
the identity is then at least `F(n + 1)F(n)`, while its right side is at most
`2nF(n + 1)` because `F(j + 1) ≥ 1`. Cancelling the positive factor `F(n + 1)`
gives `F(n) ≤ 2n`, which contradicts `2n < F(n)` for `n ≥ 8`. That last bound is
an induction: it holds at `n = 8` since `F(8) = 21 > 16`, and the step adds
`F(n − 1) ≥ F(7) = 13 > 2` to `F(n)`.

## Falsifier

A single `n ≥ 1` with `F(n + 2) + 2nF(n + 1)` equal to some `F(m)` refutes the
conjecture. Inside the recorded proof, the statement fails if `F(n)` and
`F(n + 1)` share a common factor for some `n`, if `2n ≥ F(n)` for some `n ≥ 8`,
or if the addition formula `F(j + n + 1) = F(j)F(n) + F(j + 1)F(n + 1)` fails for
some pair.

## Evidence

Every step of the argument was checked numerically for `n = 1` through `n = 2999`
before the proof was recorded: the rewriting `X n = F(n) + (2n + 1)F(n + 1)`, the
bracketing of `X n` between consecutive Fibonacci numbers, the addition formula
at the relevant indices, the divisibility consequence, and the bound
`2n < F(n)`. No violation occurred. Independently, `X n` was tested against the
Fibonacci numbers for `n = 0` through `n = 4000`; the only value that is a
Fibonacci number is `X 0 = 1`, which is outside the range of the conjecture and
is exactly the reason the source indexes its two sets from one.

The values of `X n` for `n = 1, …, 7` are `4, 11, 23, 48, 93, 177, 328`; the
Fibonacci numbers in that range are `1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144,
233, 377`.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9382
before the proof was recorded. The admission basis is `escape-witness` with
`proof_shape: content`; the declared escape content is the bound `2n < F(n)` for
`n ≥ 8` obtained by induction, the rearranged identity
`(F(j) − 1)F(n) = (2n + 1 − F(j + 1))F(n + 1)`, and the divisibility consequence
`F(n + 1) ≤ F(j) − 1`. The computational use is `none`: the delivered statement
is a universally quantified theorem with no bounded enumeration, checker, numeric
reduction or certified instance among its declarations.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article and its abstract page, the
OEIS entries A248982 and A007502, and the withdrawn preprint arXiv:2509.26138
were opened. That preprint, whose Theorem 23 and Proposition 24 addressed this
conjecture, was withdrawn by its author on 2025-11-06 with the comment "This
paper has been withdrawn by Duc Hieu Le"; the withdrawal was confirmed directly
on the arXiv abstract page. The *Journal of Integer Sequences* assigns no DOI and
citation-index result pages were not reachable, so no worldwide priority claim is
made.

The closed-form description of A248982 for `n ≥ 10`, which the source states
alongside the conjecture, is not settled here. Disjointness of the two displayed
sets is one ingredient of it; the remaining content is the identification of
`(a_n)` with those values.
