---
slug: oeis-a119690-layman-odd-power-factorial-residue
bibkey: lava2010a119690
doi: null
url: https://oeis.org/A119690
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime
  - D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.result
---

# Layman's odd-power factorial residue classification

## Problem

OEIS A119690, NAME (`%N`, verbatim):

> n! mod n*(n+1)/2.

John W. Layman's target COMMENT (`%C`, verbatim):

> It appears that f(n)=(n!)^(2k+1) modulo n(n+1)/2 is n if n is one less than an odd prime, else f(n) is 0, for any integer k. See A175567 for related results involving an even power of n!. - _John W. Layman_, Jul 12 2010

The entry's FORMULA (`%F`, verbatim):

> a(n) = n if n+1 is an odd prime, a(n) = 0 otherwise.

The literal proved statement is

`forall n k : Nat, 1 <= n -> (n!)^(2*k+1) mod (n*(n+1)/2) = if
Prime(n+1) and Odd(n+1) then n else 0`.

The FORMULA is the `k = 0` case and is already presented by the entry as a
formula, not a conjecture. The new settlement is Layman's generalization to
all odd powers `2*k+1`; no priority is claimed for the `k = 0` case.

Not claimed here are A175567 or any result about even powers, the COMMENT
`All terms are even`, or any other property of A119690.

## Motivation

Layman's 2010 comment asks whether the residue classification already stated
for `n!` persists for every odd power of `n!`. The theorem proves that exact
universal extension for every natural `n>=1` and every natural exponent
parameter `k`.

## Gap

On 2026-09-15, all 16 revisions of A119690 and the linked A175567 entry were
checked. Layman's statement remained worded `It appears that`, and neither
entry supplied a proof. Exact-ID and mathematical-shape queries in arXiv,
Crossref, and the repository found no settlement in the checked scope.
OpenAlex was not checked because its daily quota returned HTTP 429.

Repository, pinned Mathlib, Loogle, and LeanSearch queries found the Wilson,
factorial-divisibility, parity, and coprimality ingredients but no declaration
yielding `factorial_dvd_triangular_of_not_odd_prime` by binding and
normalization. No exhaustive literature or priority claim is made.

## Route

When `n+1` is an odd prime, `n` is even and the modulus factors as
`(n/2)*(n+1)` with coprime factors. Wilson's theorem gives
`n! = -1 = n` modulo `n+1`, while `n/2` divides `n!`. Raising to `2*k+1`
preserves both components: minus one stays minus one modulo `n+1`, and zero
stays zero modulo `n/2` because the exponent is positive. The coprime product
criterion combines them into the required residue modulo `n(n+1)/2`.

In every other branch, the public lemma proves that the triangular modulus
divides `n!`. Its even-`n`, odd-composite-`n+1` case writes `n+1=a*b`; parity
proves `a+b<a*b`, uniformly including the square case `a=b`. It embeds
`a!*b!` through `(a+b)!` into `n!` and combines the resulting `n+1` divisor
with `n/2` by coprimality. The odd-`n` branch similarly combines `n` with
`(n+1)/2`.

## Falsifier

Any natural `n>=1` and `k>=0` whose computed residue differs from the stated
conditional value would contradict `result`. For the reusable lemma, any
`n>=1` with `n+1` not an odd prime for which `n(n+1)/2` does not divide `n!`
would be a counterexample.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.lean`.
- Public lemma: `factorial_dvd_triangular_of_not_odd_prime`, with std3 axiom
  closure `[propext, Classical.choice, Quot.sound]`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 4.82 seconds, type checking
  37.9 milliseconds, and maximum resident set size 2,134,736,896 bytes.
- Deleting the sole direct import `Mathlib.NumberTheory.Wilson` makes the
  module fail to compile with exit 1; restoring it gives a zero-exit build.
- An independent scan over `n=1,...,2999` and `k` in `{0,1,2,5}` found zero
  mismatches.
- A separate scan over `n=1,...,10000` and `k=0,...,31` checked 320,000
  pairs, with 1,228 odd-prime branches, 8,772 zero branches, and zero
  mismatches.
- The bounded scans carry no proof and sample the universal over `k` only.

## Triage

`theorem`. Layman's all-odd-powers generalization is proved for every natural
`n>=1` and `k>=0`; the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Literature completeness outside the checked OEIS revisions, linked A175567,
arXiv, Crossref, repository, pinned Mathlib, Loogle, and LeanSearch surfaces
is unverified. The bounded scans do not establish the universal statement and
sample its universal quantifier over `k`; no exhaustive literature or
priority claim is made.
