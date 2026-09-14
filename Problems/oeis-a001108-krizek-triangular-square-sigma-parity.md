---
slug: oeis-a001108-krizek-triangular-square-sigma-parity
bibkey: sloane2016a001108
doi: null
url: https://oeis.org/A001108
triage: theorem
motivation_gids:
  - D5/S3/Arith/KrizekTriangularSquareSigmaParity
---

# The A001108 triangular-square indices have two odd divisor sums

## Problem

OEIS A001108, NAME (`%N`, verbatim):

> a(n)-th triangular number is a square: a(n+1) = 6*a(n) - a(n-1) + 2, with a(0) = 0, a(1) = 1.

Jaroslav Krizek's COMMENT conjecture (`%C`, verbatim, with its preceding
context sentence):

> The squares of NSW numbers (A008843) interleaved with twice squares from A084703, where A008843(n) = A002315(n)^2 and A084703(n) = A001542(n)^2. Conjecture: Also numbers n such that sigma(n) = A000203(n) and sigma(n-th triangular number) = A074285(n) are both odd numbers. - _Jaroslav Krizek_, Aug 05 2016

The literal proved statement is
`forall n : Nat, 0 < n -> (IsSquare (n * (n + 1) / 2) iff
(Odd (sigma 1 n) and Odd (sigma 1 (n * (n + 1) / 2))))`.
The recurrence for A001108, Pell-type completeness, the NSW/A084703
interleaving structure, and all other A001108 comments are NOT claimed. The
guard excludes `n=0`: although `T_0=0` is a square, Mathlib defines
`sigma(0)=0`, which is even, so the unguarded parity equivalence is false.

## Motivation

Krizek's comment proposes an intrinsic divisor-sum test for membership among
the triangular-square indices. The theorem turns that bounded observational
criterion into a classification for every positive natural index without
claiming a recurrence or a Pell parametrization.

## Gap

On 2026-09-15, OEIS revision 330 still printed Krizek's August 2016 statement
as a "Conjecture". The probe checked revisions 221 through 330 and found no
proof or refutation. Gionata Neri's April 30, 2018 comment reformulates the
condition through odd divisors of `n` and `n+1` but supplies no proof.

The 2026-09-15 recheck found zero arXiv results for `A001108`; its broader
triangular-number/divisor-sum query returned two unrelated papers. OpenAlex
returned zero results for the exact conjecture phrase, while its eight
`A001108` search records were unrelated by title. MathOverflow returned zero
exact results; its one broad result concerned `sigma(square)=prime`, not this
characterization. The probe also found zero exact GitHub phrase matches.
These checked surfaces do not support an exhaustive literature or priority
claim.

## Route

1. Prove the classical characterization that a positive natural number has
   odd divisor sum exactly when it is a square or twice a square.
2. For consecutive coprime `n` and `n+1`, split an identity
   `n(n+1)=2b^2` between the two factors. This forces one factor to be a
   square and the other twice a square.
3. Exclude a triangular number of the form `2f^2` when its positive index is
   itself a square or twice a square.
4. Apply the parity characterization to the index and its triangular number.
   The coprime-product split proves the forward implication, and the
   twice-square exclusion leaves an actual square in the reverse implication.

The sigma-parity characterization is re-proved as a private bidirectional
lemma. Its forward direction also appears in the private, non-importable
`square_or_twice_square_of_sigma_odd` lemma in the landed Lagneau module from
pull request 7579; that classical re-proof is disclosed but is not an escape
witness.

## Falsifier

Any positive natural `n` for which `n(n+1)/2` is square while either divisor
sum is even, or for which both divisor sums are odd while `n(n+1)/2` is not
square, would contradict the theorem. The kernel-checked result quantifies
over every positive natural `n`.

## Evidence

- Lean module: `D5/S3/Arith/KrizekTriangularSquareSigmaParity.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 6.69 seconds, type checking
  120 milliseconds, and maximum resident set size 1,723,138,048 bytes.
- Deleting either direct Mathlib import makes the module fail to compile;
  restoring both gives a zero-exit single-file profile build.
- The orchestrator and probe found zero mismatches for `1 <= n <= 2*10^6`.
  The members at most `10^6` were
  `1, 8, 49, 288, 1681, 9800, 57121, 332928`, matching the OEIS data.
- At `n=0`, the independent boundary check gives a square triangular number
  and an even divisor sum, confirming the need for the positive guard.
- The bounded checks support fault detection only; the Lean factorization and
  exclusion arguments carry the universal statement.

## Triage

`theorem`. Krizek's divisor-sum characterization is proved for every natural
`n` satisfying `0 < n`; the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

The bounded scans do not establish the universal statement. Historical
openness outside the checked OEIS history, arXiv, OpenAlex, MathOverflow, and
GitHub surfaces is unverified; no exhaustive literature or priority claim is
made.
