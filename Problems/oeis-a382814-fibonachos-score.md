---
slug: oeis-a382814-fibonachos-score
bibkey: kagey2025a382814
doi: null
url: https://oeis.org/A382814
triage: theorem
motivation_gids:
  - D5/S3/Arith/FibonacciAtomic/FibonachosScore
---

# Fibonachos ties and first-player majority

## Problem

Peter Kagey's OEIS A382814 comment states:

> Conjecture:
> a(n) = n/2 if and only if n is in {2, 8, 10, 32}.

> Conjecture:
> For n > 32, a(n) > n/2 if and only if F(m)-1 <= n <= F(m+1)-2 for some odd integer m, where F(n) = A000045(n).

The two players alternate taking successive Fibonacci numbers, beginning
with `F(1)=F(2)=1`. When the next number exceeds the remaining heap, the
index resets to one; the player's turn still alternates. The game stops
at the empty heap, and `a(n)` is the first player's total.
For every positive integer `n`, the tie condition is `2a(n)=n`.
For every `n>32`, first-player majority is `n<2a(n)` and the block
condition has an existential natural index `m` with `Odd m`.

The formal interval is `F(m)<=n+1` and `n+2<=F(m+1)`. In this range the
upper condition forces a positive, nontruncated upper endpoint, and
these are equivalent to the displayed source inequalities. Multiplying
the score comparison by two avoids natural-division rounding.

## Motivation

This is a tier-one named external problem. Issue #12461 fixes the two
literal comments, complete quantifiers, proposed resolution and bounded
prior-work checks before the probe. Both assertions share one `result`.

## Gap

The checked internal OEIS entry still labels both assertions Conjecture.
The checks in #12461 include the current entry, author discussion, related
Fibonachos restart-count work, named OEIS-conjecture papers, formal-problem
inventories and this repository. Those external-search reports are supplied
by the preregistration, rather than independently reproduced here.
Additional Loogle name searches and GitHub Lean code searches for
`Fibonachos` and `A382814` have no matches. The OEIS internal entry, history page and
b-file were accessible; the text interface returned HTTP 403. Individual
historical revisions were not exhaustively inspected. This bounded search makes no first-proof claim.

## Route

Let `D(n)=2a(n)-n`. For `m>=3`, a heap in the interval
`F(m)-1<=n<=F(m+1)-2` begins with exactly `m-2` uninterrupted moves.
Their sum is `F(m)-1`. The alternating sum and subsequent player swap,
with `r=n-(F(m)-1)<F(m-1)`, yield
`D(n)=1+(-1)^m(D(r)-F(m-3))`.

For `t>=4` and `0<=u<F(t)`, induction gives
`|D(u)-1|<=F(t-3)`. A smaller heap uses the previous bound. At
`u=F(t)-1`, the remainder is zero and the bound is attained.
The remaining heaps use block index `t-1` and a remainder below `F(t-2)`.
For `n>32`, the block index is at least nine; the remainder estimate
makes `D(n)` strictly positive in odd blocks and strictly negative in
even blocks. The positive heaps at most 32 have exactly four ties.

## Falsifier

A positive heap outside the four listed ties with `2a(n)=n`, a listed
heap without a tie, or a heap greater than 32 whose majority differs from
its Fibonacci-block parity would refute the respective assertion.
A function failing the source's reset or player-swap rule would not
formalize this game. Finite examples alone cannot establish the two
universal assertions.

## Evidence

`D5/S3/Arith/FibonacciAtomic/FibonachosScore.lean` defines the recursive
score pair and first-player total. Its sole public theorem `result`
conjoins both universally quantified source assertions. The proof contains
the first ten values, total-score conservation, the block formula, the
uniform bound and the small-heap classification. All finite evaluations
use proof-producing kernel reduction, with no native decision axiom.
Kernel verification, source fidelity, freezing and merge are distinct.

## Triage

`theorem`; resolution `proved`; admission basis `open-problem-resolution`;
`proof_shape: bind-only`. After unfolding the game, the proof uses natural
induction, Fibonacci recurrence, parity, finite branches and arithmetic
normalization. No independent escape witness is claimed.

### What the settlement shows

Proved in the proof of `D5/S3/Arith/FibonacciAtomic/FibonachosScore.result`:
the reset decomposition and uniform error bound are the mechanism for both
classifications. The estimate is sharp: at `u=F(t)-1`, the empty remainder
has `D(0)=0`, so the block formula gives
`|D(u)-1|=F(t-3)`. These are internal proof facts, not additional public
theorems. The first ten scores and the tie classification through 32 are
kernel computations within that proof.

Open: analogous classifications for different reset indices, different
player alternation rules or other recurrence sequences. The argument
would require a corresponding prefix sum, signed prefix identity and
remainder bound; none is proved here. No further conclusion in the
checked OEIS comment block is stated as depending on these two conjectures.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources above. The preregistration's
reports of a full historical search and author-discussion checks were not
independently reproduced here. No global novelty or publication-priority
claim is made. Source fidelity and the additive interval translation remain
subject to independent review. Generalized reset rules and recurrence
sequences remain open.
