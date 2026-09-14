---
slug: oeis-a260407-krizek-all-multiples-of-the-order
bibkey: hasler2016a260407
doi: null
url: https://oeis.org/A260407
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder
---

# The A260407 condition holds at every positive multiple of the order

## Problem

OEIS A260407, NAME (`%N`, verbatim):

> Numbers n such that (n-1)^2+1 divides 2^(n-1)-1.

Jaroslav Krizek's COMMENT (`%C`, verbatim):

> Conjecture: also numbers n such that ((2^k)^(n-1)-1) == 0 mod ((n-1)^2+1) for all k >= 1. - _Jaroslav Krizek_, Jun 02 2016

Define `modulus(n) = (n-1)^2+1`, using natural-number subtraction. The
literal proved statement is `forall n : Nat, 1 <= n -> (inSequence n iff
allMultiples n)`, where `inSequence n` means
`modulus(n) divides 2^(n-1)-1`, and `allMultiples n` means that for every
natural `k >= 1`, `modulus(n) divides 2^(k*(n-1))-1`. The equality
`(2^k)^(n-1) = 2^(k*(n-1))` identifies the COMMENT exponent with the
formal exponent.

The claim that `a(7) = 1382401` is the first composite term, the claim that
the Fermat numbers `2^(2^k)+1` for `k > 1` form a subsequence, Hasler's
further conjecture that those numbers are the intersection with A260406,
anything about A260406 or A260072, and every other A260407 comment are NOT
claimed. The textbook divisibility fact for arbitrary `m` and `d` is also
not claimed as a new result.

## Motivation

Krizek's comment asks whether the defining divisibility condition for
A260407 already characterizes divisibility at every positive multiple of
the exponent. The theorem settles that exact set equality for every natural
`n >= 1`.

## Gap

On 2026-09-15, all OEIS A260407 revisions #1 through #24 were read. The
target comment first appears in revision #17 and remains marked
"Conjecture" in revision #24, with no proof, refutation, or withdrawal.

The arXiv query `all:"A260407"` returned zero results, and the query
`"order of 2 modulo (n-1)^2+1"` returned zero results. The query
`"2^(n-1)" AND "(n-1)^2+1"` returned nine token matches; title and abstract
inspection found zero statements of this equivalence. These checked
surfaces do not establish exhaustive literature coverage, and no priority
claim is made.

## Route

For the forward implication, take the divisibility at exponent `n-1` and
compose it with Mathlib's fact that `2^d-1` divides `2^e-1` when `d` divides
`e`; here `d=n-1` divides `k*(n-1)`. For the converse, specialize the
universal statement at `k=1` and normalize the exponent.

After the three definitions are unfolded, this proof is bind-only over the
pinned Mathlib divisibility lemma. The underlying general divisibility fact
is textbook material and is not claimed as new; the result settles the
named OEIS comment.

## Falsifier

Any natural `n >= 1` for which exactly one of the NAME condition and the
positive-multiple condition holds would contradict the theorem. The
kernel-checked result quantifies over every such natural `n` and every
positive natural `k` on the all-multiples side.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/KrizekAllMultiplesOfTheOrder.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- The definitions `modulus`, `inSequence`, and `allMultiples` each have
  axiom closure `[propext]`.
- Kernel profile on this worktree: wall time 8.12 seconds, type checking
  1.21 milliseconds, and maximum resident set size 1,481,998,336 bytes.
- Deleting the sole direct import `Mathlib.Algebra.Ring.GeomSum` makes the
  module fail to compile; restoring it gives a zero-exit profile build.
- The independent bounded scan covered `n=2,...,59999` and sampled the
  universal condition through `k=24`, finding zero equivalence violations.
- At `n=1`, `modulus(1)=1` and `2^0-1=0`, so both sides are true.
- The bounded scan and boundary evaluation support fault detection only;
  they carry no proof of the universal statement.

## Triage

`theorem`. Krizek's equivalence is proved for every natural `n >= 1`; the
resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

The bounded scan does not establish the universal statement, and its
universal side was sampled only through `k=24`. Historical openness outside
the checked OEIS revisions and literature-query surfaces is unverified; no
exhaustive literature or priority claim is made.
