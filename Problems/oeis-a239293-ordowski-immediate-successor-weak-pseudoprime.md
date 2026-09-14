---
slug: oeis-a239293-ordowski-immediate-successor-weak-pseudoprime
bibkey: ferreol2018a239293
doi: null
url: https://oeis.org/A239293
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime
---

# The immediate successor is the least weak pseudoprime exactly when it is an odd composite

## Problem

OEIS A239293, NAME (`%N`, verbatim):

> Smallest composite c > n such that n^c == n (mod c).

The neighbouring terminology COMMENT (`%C`, verbatim):

> a(n) is the smallest weak pseudoprime to base n that is > n.

The neighbouring sufficient-condition COMMENT (`%C`, verbatim):

> If n is even and n+1 is composite, then a(n) = n+1. [Corrected by _Thomas Ordowski_, Aug 03 2018]

Thomas Ordowski's target COMMENT (`%C`, verbatim):

> Conjecture: a(n) = n+1 if and only if n+1 is an odd composite number. - _Thomas Ordowski_, Aug 03 2018

The literal proved statement is

`forall n : Nat, 1 <= n -> ((1 < n+1 and not Prime(n+1) and n^(n+1) mod
(n+1) = n mod (n+1)) iff (not Prime(n+1) and Odd(n+1) and 1 < n+1))`.

By the NAME, `a(n)` is the least composite `c>n` satisfying the displayed
congruence. Since `n+1` is the immediate successor of `n`, no natural number
lies strictly between them. Thus `a(n)=n+1` holds exactly when `n+1` itself
qualifies; minimality at the immediate successor is automatic. This is the
reduction used by the theorem, and it does not require a total definition of
`a` at bases for which no qualifying composite has been supplied.

The neighbouring sufficient-condition COMMENT is not claimed as a new
result. The weak-pseudoprime terminology COMMENT is not claimed as a new
result. Totality of `a` is not claimed; proving it would require a different
existence theorem asserting a qualifying composite above every base.

## Motivation

Ordowski's 2018 comment asks for an exact characterization of the bases at
which the first possible modulus, `n+1`, is already the sequence value. The
formal biconditional settles this named conjecture while keeping the separate
totality question outside its statement.

## Gap

On 2026-09-15, the OEIS current text and revisions #1 through #27 were
checked. The target appears only as Ordowski's 2018 Conjecture, with no later
proof, refutation, or withdrawal. The OEIS exact-quote search returned only
A239293. Twelve Ordowski or weak-pseudoprime OEIS entries were inspected and
contained no second statement or settlement of the conjecture. The Numericana
page linked from the entry was also checked and supplied no settlement.

These checked surfaces do not establish exhaustive literature coverage, and
no priority claim is made. A pinned Mathlib and repository search found the
residue and parity facts used below but no theorem stating the complete
A239293 equivalence.

## Route

Modulo `n+1`, the base satisfies `n = -1`. Therefore
`n^(n+1) = (-1)^(n+1)` modulo `n+1`. If `n+1` is odd, this power is `-1`, so
the required congruence holds. If `n+1` is even, the power is `1`; equality
with `-1` would force `n+1` to divide 2, hence `n+1=2`. That boundary modulus
is prime and therefore cannot satisfy the composite condition.

After the local `have` statements are inlined, the proof is bind-only over
the pinned Mathlib results `ZMod.natCast_self'`,
`ZMod.natCast_eq_natCast_iff'`, `Odd.neg_one_pow`, `Even.neg_one_pow`,
`ZMod.neg_one_ne_one`, and `Nat.prime_two`. The remaining steps are
instantiation, projection, rewriting, and arithmetic normalization.

## Falsifier

Any natural `n>=1` for which exactly one side of the formal biconditional
holds would contradict `result`. A base for which no qualifying composite
above `n` exists would instead refute totality of the OEIS sequence; it would
not contradict the theorem because totality is not asserted.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 9.08 seconds, type checking
  1.68 milliseconds, and maximum resident set size 1,615,347,712 bytes.
- Deleting the sole direct import `Mathlib.Data.ZMod.Basic` makes the module
  fail to compile; restoring it gives a zero-exit profile build.
- Direct computation of `a(n)` from the NAME for `n=1,...,3999` found every
  value, with largest `a(n)=5611`, and found zero pointwise mismatches with
  the odd-composite characterization.
- The reduced biconditional was checked for `n=1,...,199999` and had zero
  mismatches.
- The bounded scans support fault detection only; they carry no proof of the
  universal statement.

## Triage

`theorem`. Ordowski's immediate-successor characterization is proved for
every natural `n>=1`; the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

The bounded scans do not establish the universal statement. Literature
completeness outside the checked OEIS revisions, exact-quote result,
Ordowski and weak-pseudoprime entries, linked Numericana page, pinned
Mathlib, and repository searches is unverified; no exhaustive literature or
priority claim is made.
