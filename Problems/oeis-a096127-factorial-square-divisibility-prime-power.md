---
slug: oeis-a096127-factorial-square-divisibility-prime-power
bibkey: murthy2004a096127
doi: null
url: https://oeis.org/A096127
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower
---

# Exact factorial-square divisibility in A096127

## Problem

OEIS A096127, NAME (verbatim):

> a(n) is the largest k such that (n^2)!/(n!)^k is an integer.

COMMENT (verbatim):

> Conjecture: a(n)=n+1 only when n is prime or a power of a prime. [Verified for n=2..5000. - _Amiram Eldar_, Apr 06 2021]

OEIS A096126 states the same assertion. The A096127 offset is 2.

## Motivation

The conjecture asks for an unbounded characterization of the indices where
the first universally valid exponent is exact. Proving the biconditional
settles both the stated only-if direction and the converse recorded in the
neighboring OEIS material.

## Gap

On 2026-09-13 the preregistration search checked the A096127, A096126,
A057599, and A034841 entries and histories; Crossref; OpenAlex; arXiv;
MathOverflow; Math StackExchange question 979886 and both answers; GitHub
issues; Internet Archive; Karpov's 2017 note linked from A057599; and
arXiv:2410.22287 linked from A034841. The complete biconditional was not
found in the checked surfaces. Semantic Scholar and GitHub code search were
not verified because their requests returned 429 and 401 respectively;
Google Scholar and MathSciNet were not checked.

## Route

Legendre's formula writes
`v_p(m!) = (m - s_p(m))/(p-1)`, where `s_p` is the base-`p` digit sum. The
key estimate is digit-sum submultiplicativity
`s_p(n^2) <= s_p(n)^2`. For `s = s_p(n)`, the exponent `k=n+1` reduces to
`(s-1)(s-n) <= 0`, which always holds. The exponent `k=n+2` reduces to
`(s-2)(s-n) <= 0`, equivalently `s_p(n) >= 2`, equivalently `n` is not a
power of `p`. Thus a non-prime-power `n` admits exponent `n+2` at every
prime, while for `n=p^e` the valuation at `p` fails exactly at exponent
`n+2`.

## Falsifier

Any natural `n >= 2` for which the conjunction
`(n!)^(n+1) | (n^2)!` and `not ((n!)^(n+2) | (n^2)!)` differs from
`IsPrimePow n` would refute the theorem. A failure of digit-sum
submultiplicativity at any prime base would invalidate the common estimate.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower.lean`.
- Main theorem: `factorial_square_exact_divisibility_iff_prime_power`.
- The axiom report is exactly std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The probe's exact valuation check covered every `n <= 20000` with zero
  mismatches. Tight non-prime-power cases included `(n,p)=(6,5)`, `(10,3)`,
  and `(10,5)`, each with valuation slack 0.

## Triage

`theorem`. The Lean result proves the full biconditional for every natural
`n >= 2`, rather than a finite verification range.

## ASSUMED-UNVERIFIED

The OEIS wording, attribution, offset, A096126 cross-reference, revision
status, bounded literature-search results, and exact valuation check were
supplied by the preregistration and probe records. This implementation seat
read those records but did not independently repeat the external searches or
the `n <= 20000` computation. No exhaustive literature or priority claim is
made beyond the dated checked surfaces.
