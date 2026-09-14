---
slug: oeis-a226857-fibonacci-sum-product-recurrence
bibkey: barker2014a226857
doi: null
url: https://oeis.org/A226857
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence
---

# The A226857 Fibonacci sum-product recurrence is proved

## Problem

OEIS A226857, NAME (`%N`, verbatim):

> Numbers that are both the sum of two Fibonacci numbers and the product of two Fibonacci numbers.

FORMULA conjecture line (`%F`, verbatim):

> Conjecture: a(n) = a(n-3)+a(n-6) for n>12. - _Colin Barker_, Nov 09 2014

Empirical generating function (`%F`, verbatim):

> Empirical g.f.: -x^2*(x^10 +x^9 +x^8 +2*x^7 +3*x^6 +3*x^5 +3*x^4 +3*x^3 +3*x^2 +2*x +1) / (x^6 +x^3 -1). - _Colin Barker_, Nov 09 2014

COMMENT (`%C`, verbatim):

> All Fibonacci numbers are in the sequence. The only prime numbers in this sequence are prime Fibonacci numbers.

AUTHOR (`%A`, verbatim):

> _Alonso del Arte_, Jun 19 2013

The first `%S` terms are `0,1,2,3,4,5,6,8,9,10,13,15,16,21,24,26,34,39,42,55,63,68,89,102,110`.

The literal proved statement is
`∀ n : ℕ, 12 < n → a n = a (n - 3) + a (n - 6)`, where
`mem x := (∃ i j : ℕ, x = Nat.fib i + Nat.fib j) ∧ (∃ r s : ℕ, x = Nat.fib r * Nat.fib s)`
and `a n := Nat.nth mem (n - 1)`. `Nat.nth` enumerates members from zero,
so the one-based OEIS index is represented by the subtraction `n - 1` in
natural numbers. Equal summands and equal factors are allowed. The empirical
generating-function line and the `%C` corollaries are NOT claimed.

## Motivation

The entry records a 2014 recurrence conjecture for the increasing sequence
of numbers with both Fibonacci-sum and Fibonacci-product representations. The
formal classification of the member set proves the stated recurrence for all
indices beyond twelve.

## Gap

The dated surfaces recorded in preregistration issue #7655 and its probe are
OEIS A226857's 15 revisions. The conjecture is unchanged in revisions #12
through #15 (2014-11-09/10); the only discussion note says: "The g.f. gives
the same values as those in the bfile up to n=1000". Searches of pinned
Mathlib Fib/Nth declarations found no matching theorem. A GitHub exact
`A226857` search returned only OEIS mirrors and #7655. Crossref returned 0.
The arXiv request timed out, OpenAlex returned HTTP 429, and MathOverflow
returned HTTP 403; these three surfaces are `ASSUMED-UNVERIFIED`. No priority
claim is made.

## Route

1. The product gap invariant proves, by two-step double induction, the strict
   interval in the product indices. Its base points are `(5,5): 24<25<26`,
   `(5,6): 39<40<42`, and `(6,6): 63<64<68`.
2. The index-exclusion lemma rules out a sum representation for products with
   both factors at least five.
3. The membership predicate is therefore classified exactly by the three
   families `{F_k, 2F_k, 3F_k}`.
4. The interleaving `F_{k+2} < 3F_k < 2F_{k+1} < F_{k+3}` for `k ≥ 4`
   identifies the explicit increasing enumeration with `Nat.nth mem`.
5. Each of the three subsequences satisfies the Fibonacci recurrence, giving
   the three-and-six-step recurrence for `a`.

## Falsifier

A counterexample to `a(n) = a(n-3) + a(n-6)` at some natural `n > 12`, under
the stated `mem` and `a` definitions, would contradict the theorem. The
kernel-checked theorem covers every such `n`.

## Evidence

- Lean module: `D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.lean`.
- Main theorem: `barker_a226857`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Orchestrator checks from #7655: members at most `10^9` are exactly
  `{F_k, 2F_k, 3F_k}`; there are 124 members, with last value `866,988,874`.
  The recurrence has no violation for `13 ≤ n ≤ 124`; the gap invariant holds
  for all `5776` pairs with `5 ≤ r, s ≤ 80`; and the interleaving holds for
  `4 ≤ k ≤ 100`.
- The enumeration formula was checked for `4 ≤ k ≤ 41`:
  `a(3k−4) = F_{k+2}`, `a(3k−3) = 3F_k`, and
  `a(3k−2) = 2F_{k+1}`. The probe independently reported the same readings.
- The generating-function line and the `%C` statements are supporting source
  material only and are not formalized here.

## Triage

`theorem`. The recurrence is proved for every `n > 12` from the exact
membership predicate and one-based enumeration specified above.

## ASSUMED-UNVERIFIED

The arXiv timeout, OpenAlex HTTP 429, and MathOverflow HTTP 403 leave those
search surfaces incomplete. The bounded enumerations and the literature
search do not establish exhaustive coverage or publication priority.
