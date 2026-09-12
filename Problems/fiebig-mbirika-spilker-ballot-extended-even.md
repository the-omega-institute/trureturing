---
slug: fiebig-mbirika-spilker-ballot-extended-even
bibkey: fiebigmbirikaspilker2025lucas
doi: null
url: https://arxiv.org/abs/2408.14632v2
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LucasEvenPeriods
---

# Equality of Lucas periods when p and m are both even, at q = -1

## Problem

Question 5.3 of arXiv:2408.14632v2, as printed:

> Subsection 3.4 begins with a convention restricting the `p` and `m` values to either of the
> following classes: (1) `p` is odd, or (2) `p` is even and `m` is odd. ... However, data
> generated with Mathematica provides ample support that when `q = -1`, the corollary holds even
> in the setting when both `p` and `m` are even. This remains an open problem.

The corollary being extended reads: "Let `m > 2` be given and set `V_n := V_n(p,q)`. If `e_V(m)`
exists, then we have `pi_U(m) = pi_V(m)` if either condition holds: (1) `p` is odd, or (2) `p` is
even and `m` is odd."

## Motivation

The convention that excludes this case is not cosmetic. The paper's route to the corollary runs
through Ballot's equality theorem with a gcd input, and for even `p` every `V_n` is even, so the
gcd it needs equals `2` when `m` is even. The sufficient condition genuinely fails, so extending
the corollary requires a different argument rather than a wider hypothesis.

## Gap

The paper proves the corollary only under its own convention and records the even-even case as
open on numerical evidence.

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

Even `p`, even `m > 2`, `q = -1`, a positive companion zero modulo `m`, and `pi_U(m) != pi_V(m)`
would refute it.

## Evidence

- Module: `D5/S1/Recurrence/LucasEvenPeriods.lean`, frozen.
- Theorem: `even_lucas_periods`, an `iff` whose exceptional case is
  `q = 1 and m = 4 and 4 divides p`. At `q = -1` that case cannot occur, so the equality holds
  throughout the regime this question asks about.
- The odd-part input is the frozen `companionPeriod_eq_matrixPeriod_of_lucasV_zero` in
  `D5/S1/Recurrence/LucasCompanion.lean`, which removes the dependence on McDaniel's 1991 gcd
  theorem that the paper's own route uses.
- **The machine-readable resolution marker for this question sits on the sibling entry**
  `fiebig-mbirika-spilker-even-period-exception`, because one Blueprint node carries one
  resolution claim and a single theorem settles both questions.
- Orchestrator scan, over `p` even in `2..80`, `q` in `{1,-1}`, `m` even in `4..300` — so `m = 2`
  is outside the window, as the theorem excludes it — with `gcd(q,m) = 1`, `e_V(m)` existing, and
  the paper's degenerate pairs `(p,q)` in `{(2,1),(-2,1),(1,1),(-1,1),(0,1),(0,-1),(1,0),(-1,0)}`
  excluded: 2306 cases, 20 of them the exceptional one, zero disagreements with the biconditional.

## Triage

`theorem`. The `q = -1` case this question asks about is settled, as a consequence of the sharper
biconditional recorded on the sibling entry. Not settled here: the same question for the
companion sequence's zero set rather than its trace.

## ASSUMED-UNVERIFIED

The scan count is an orchestrator reading, not a machine-checked fact. The identification of the
paper's `pi_U`, `pi_V` and `e_V` with the repository's `matrixPeriod`, `companionPeriod` and the
positive-zero criterion is a reading of the paper's definitions. First-publication priority is not
established, and no forum search was performed.
