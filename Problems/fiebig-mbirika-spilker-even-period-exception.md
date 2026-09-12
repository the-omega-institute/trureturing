---
slug: fiebig-mbirika-spilker-even-period-exception
bibkey: fiebigmbirikaspilker2025lucas
doi: null
url: https://arxiv.org/abs/2408.14632v2
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LucasEvenPeriods
---

# The single exceptional modulus for equality of even Lucas periods

## Problem

Question 5.4 of arXiv:2408.14632v2, as printed:

> ... when `p = 0 (mod 4)`, then it appears that the corollary holds for all even values `m > 2`
> except for the single value of `m = 4`. And in that case, we have `e_V(4) = 1` but
> `pi_U(4) = 4 != 2 = pi_V(4)` ... However, when `p = 2 (mod 4)` and `m > 2` is even, the
> existence of `e_V(m)` appears to always guarantee that `pi_U(m) = pi_V(m)`. Can we prove that
> the corollary holds for all even values `p` and `m` with `m > 2`, except in the singular case
> when `m = 4` and `p = 0 (mod 4)`?

The excerpt is taken from a subsection whose standing hypothesis is `q = 1`, so the exceptional
case has **three** conditions, not two: `q = 1`, `m = 4`, and `4` dividing `p`. That matters
because with `q = -1` the same modulus and the same divisibility give **equal** periods, which is
what the sibling entry `fiebig-mbirika-spilker-ballot-extended-even` records. The theorem below
carries all three conditions in its exceptional clause.

## Motivation

This is the sharp form of the previous question. It does not merely ask whether the equality
extends; it asserts that a single modulus is the only obstruction, which makes it a biconditional
rather than an implication and pins down where the argument must break.

## Gap

The paper gives the exceptional case numerically and asks for a proof. Proving only the
implication would leave the sharpness unproved, and the sharpness is the whole content.

## Route

Work with the companion matrix `M = !![p, -q; 1, 0]` over `ZMod m`; `pi_U` is its order in the
unit group and `pi_V` the least period of its trace. Two reductions carry the answer. First,
writing `M^{pi_V} = I + N`, the identity `pi_U = pi_V * ord(N)` turns the question into whether
`N = 0`. Second, the Chinese remainder factorisation `m = 2^v * s` with `s` odd separates the two
obstructions: on the odd part `2` is a unit, so the frozen
`companionPeriod_eq_matrixPeriod_of_lucasV_zero` applies directly; on the dyadic part a companion
zero forces `M^2 = -q`, and for `q = 1` the trace sequence drops its period exactly when `2 = -2`,
which happens exactly at `v = 2`. That is where the single exceptional modulus comes from.

## Falsifier

Even `p`, even `m > 2`, a unit `q`, a positive companion zero modulo `m`, and either
`pi_U(m) != pi_V(m)` outside the case `q = 1, m = 4, 4 | p`, or `pi_U(m) = pi_V(m)` inside it.

## Evidence

- Module: `D5/S1/Recurrence/LucasEvenPeriods.lean`, frozen.
- Theorem: `even_lucas_periods`, stated as an `iff`:
  `matrixPeriod = companionPeriod` holds exactly when `not (q = 1 and m = 4 and 4 divides p)`.
  The biconditional form is what proves the exception is the only one.
- The odd-part input is the frozen `companionPeriod_eq_matrixPeriod_of_lucasV_zero` in
  `D5/S1/Recurrence/LucasCompanion.lean`, which removes the dependence on McDaniel's 1991 gcd
  theorem. That lemma was measured over `q` in `-7..7` nonzero, `p` in `0..25`, `s` odd in
  `3..139` with `gcd(q,s) = 1` and a companion zero modulo `s`: 10389 cases, zero failures, and
  it restricts neither `p` to even nor `q` to plus or minus one. That window has `s` odd, so no
  even modulus enters it and in particular `m = 2` does not.
- The reduction `pi_U = pi_V * ord(N)` was measured over `p` even in `2..60`, `q` in `{1,-1}`,
  `m` even in `4..200` — so `m = 2` is outside the window — excluding the eight degenerate pairs
  `(p,q)` in `{(2,1),(-2,1),(1,1),(-1,1),(0,1),(0,-1),(1,0),(-1,0)}` and requiring `e_V(m)` to
  exist: 1253 triples, zero mismatches; the 15 failures of `pi_U = pi_V` in that window are uniformly
  `q = 1`, `m = 4`, `p = 0 (mod 4)`.
- Biconditional scan, over `p` even in `2..80`, `q` in `{1,-1}`, `m` even in `4..300` — `m = 2`
  outside the window, as the theorem excludes it — with `gcd(q,m) = 1`, `e_V(m)` existing, and the
  same eight degenerate pairs excluded: 2306 cases, 20 of them the exceptional one, zero
  disagreements. A scan in which the exception never occurs would not have tested that half.

## Triage

`theorem`. The biconditional is settled for every even `p`, every even `m > 2` and every integer
unit `q`, **under the hypothesis that a positive companion zero exists modulo `m`** — the
existence of `e_V(m)` that the question itself assumes. It also settles the `q = -1` case recorded
on the sibling entry `fiebig-mbirika-spilker-ballot-extended-even`. Not settled here: the
analogous question for odd `p` outside the paper's own convention, and the behaviour when no
companion zero exists, where the hypothesis is vacuous and the statement says nothing.

## ASSUMED-UNVERIFIED

The three scan counts are orchestrator readings, not machine-checked facts. The identification of
the paper's `pi_U`, `pi_V` and `e_V` with the repository's `matrixPeriod`, `companionPeriod` and
the positive-zero criterion is a reading of the paper's definitions. The dyadic step of the route
was contributed by an oracle seat and then reproved in the repository; no part of the committed
proof depends on that seat's text. First-publication priority is not established, and no forum
search was performed.
