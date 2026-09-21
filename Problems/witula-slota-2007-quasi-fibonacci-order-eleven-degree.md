---
slug: witula-slota-2007-quasi-fibonacci-order-eleven-degree
bibkey: witulaslota2007order11
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL10/Slota2/slota99.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.result
---

# Degrees of the order-eleven quasi-Fibonacci polynomials

## Problem

Wituła and Słota define the five polynomial sequences by system (3.12) on
printed page 5:

> A_{n+1}(δ) = A_n(δ) + 2δB_n(δ) - δE_n(δ),
>
> B_{n+1}(δ) = δA_n(δ) + B_n(δ) + δC_n(δ) - δE_n(δ),
>
> C_{n+1}(δ) = δB_n(δ) + C_n(δ) + δD_n(δ) - δE_n(δ),
>
> D_{n+1}(δ) = δC_n(δ) + D_n(δ),
>
> E_{n+1}(δ) = δD_n(δ) + (1 - δ)E_n(δ),

with the initial values printed immediately below it:

> A_0(δ) = 1, B_0(δ) = C_0(δ) = D_0(δ) = E_0(δ) = 0.

The sentence on printed page 19 is:

> Problem. Is it true that deg A_n(∆) = deg B_n(∆) = deg C_n(∆) = deg D_n(∆) = deg E_n(∆) = n for every n = 5, 6, . . .?

Section 6 introduces `∆ := 1/δ` and writes the same polynomial family as
`A_n(∆),...,E_n(∆)`. The formal module names the indeterminate `X`. It reads
`degree` in `WithBot ℕ`, rather than `natDegree`, takes the printed threshold
literally as `5 ≤ n`, and defines the recurrence over the coefficient ring
`ℤ`.

## Motivation

The source proves only that the maximum of the five degrees is `n`. Its final
Problem asks whether every coordinate has full degree from index five onward.
The frozen declaration
`D5/S1/Recurrence/WitulaSlotaQuasiFibonacciOrderElevenDegree.result` answers
that universal question affirmatively for all natural `n ≥ 5`, including the
nonvanishing assertion implicit in equality with a finite polynomial degree.

## Gap

Issue #9270 preregisters this first-tier published Problem and its literature
check. OpenAlex record `W80948396` lists nine citing works, and no available
abstract mentions the degree question. Four accessible citing full texts were
read: the 2009 AADM paper on δ-Fibonacci numbers, the 2017 paper on
two-parametric quasi-Fibonacci numbers, the 2019 paper on quaternion
equivalents, and the 2021 paper on split-quaternions. None answers the printed
Problem.

The 2017 *Mathematica Slovaca* paper on δ-Fibonacci and δ-Lucas polynomials and
the 2013 Part II paper were unreachable and remain `ASSUMED-UNVERIFIED`.
OEIS A062883 and A189235 contain no statement about these polynomial degrees.
Three MathDB queries returned no entry for the Problem. These checked surfaces
do not establish exhaustive worldwide literature coverage, publication
priority, or the absence of an independent proof.

## Route

Let `l_n` be the vector of coefficients of `X^n` in `(A_n,B_n,C_n,D_n,E_n)`.
The live escape witness (W) is the sign-normalized leading-coefficient
invariant

`w_n = ((-1)^(n+j) [X^n] X_n)_j`.

At index five, `w_5 = (1,9,1,4,1)`. If its coordinates are
`(a,b,c,d,e)`, the recurrence gives

`w' = (2b+e, a+c-e, b+d+e, c, d+e)`.

Positivity is preserved together with `e < a+c`, because
`a'+c'-e' = 3b+e > 0`. A separate induction proves that every one of the five
polynomials has degree at most `n`. The invariant makes every coefficient of
`X^n` nonzero for `n ≥ 5`, and
`Polynomial.degree_eq_of_le_of_coeff_ne_zero` upgrades each upper bound to an
equality.

Under CLAUDE.md section 3.2, `result` has `proof_shape: content`: (W) is proved
inside the live `have` chain, is not an instance, projection, or normalization
of an existing frozen or pinned-upstream statement, is not definitionally
equivalent to the five degree equalities, and is consumed by the five
nonvanishing deductions. The module basis is `open-problem-resolution` under
the preregistration in issue #9270.

## Falsifier

Any `n ≥ 5` and any one of the five coordinates whose degree differs from `n`
would refute the result. Exact-integer recomputation of (3.12) through `n = 200`
found all five degrees equal to `n` for every `5 ≤ n ≤ 200`.

Below the asserted range, the degree vectors
`(deg A_n, deg B_n, deg C_n, deg D_n, deg E_n)` are
`(0,-∞,-∞,-∞,-∞)`, `(0,1,-∞,-∞,-∞)`, `(2,1,2,-∞,-∞)`,
`(2,3,2,3,-∞)`, and `(4,3,4,3,4)` for `n = 0,1,2,3,4`, respectively.
Thus the printed threshold `n = 5` is sharp.

## Evidence

The exact-integer recurrence sweep gives
`l_5 = (-1,9,-1,4,-1)`, `l_6 = (19,-1,14,-1,5)`, and
`l_7 = (-7,28,-7,14,-6)`, matching the alternating-sign normalization used in
(W). The source statement, printed-page locators, system (3.12), initial
values, and Section 6 notation are recorded in
`Library/Recurrence/witulaslota2007order11.md`.

The frozen theorem has statement ID
`sha256:83f74a96350070824c0f10bdbd200bb2ea415d554083885ac853128ba9800f31`.
Its axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`;
the Freeze event has no prerequisite frozen project nodes.

## Triage

First tier: a Problem printed by Wituła and Słota in *Journal of Integer
Sequences* 10 (2007), Article 07.8.5, preregistered in issue #9270.
Resolution: `proved`.

| Declaration | proof_shape | escape_witness | direct frozen dependencies | admission_basis |
| --- | --- | --- | --- | --- |
| `result` | content | (W) | none | open-problem-resolution |

The public surface is exactly `quasi`, `A`, `B`, `C`, `D`, `E`, `claim`, and
`result`. This is a symbolic theorem for every `n ≥ 5`; it is not bounded
enumeration, checker infrastructure, numeric reduction, or a certified finite
instance, so `utility: none` applies.

## ASSUMED-UNVERIFIED

The 2017 *Mathematica Slovaca* δ-Fibonacci/δ-Lucas paper and the 2013 Part II
paper are `ASSUMED-UNVERIFIED` because their full texts were unreachable. The
bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The Lean kernel does not
authenticate the external PDF, its printed pagination, the literature-search
coverage, or publication history.
