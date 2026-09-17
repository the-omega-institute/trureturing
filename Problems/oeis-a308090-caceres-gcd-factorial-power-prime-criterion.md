---
slug: oeis-a308090-caceres-gcd-factorial-power-prime-criterion
bibkey: caceres2019a308090
doi: null
url: https://oeis.org/A308090
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion
---

# Caceres' A308090 gcd-factorial-power primality criterion

## Problem

OEIS A308090, NAME (`%N`, verbatim):

> a(n) = gcd(2^n + n!, 3^n + n!, n+1).

The preceding COMMENT (`%C`, verbatim) is:

> From observation: For n > 3, if n+1 is prime, then a(n) = n+1.

The settled COMMENT (`%C`, verbatim) is:

> Conjecture: Conversely, if gcd(2^n + n!, 3^n + n!, n+1) = n+1, then n+1 is prime.

The offset is `%O 1,4`, and the AUTHOR line (`%A`, verbatim) is:

> _Pedro Caceres_, May 11 2019

The full-quantifier reading is: for every `n : Nat`, if `0 < n` and
`a n = n + 1`, then `(n + 1).Prime`, where
`a n = gcd(gcd(2^n + n!, 3^n + n!), n+1)`. The scope wall is exactly the
unsigned Conjecture sentence for every natural `n ≥ 1`. The positivity
hypothesis is part of the statement: at `n = 0`, the gcd equality holds but
`1` is not prime. The preceding one-way observation is context, not an
additional theorem in this resolution.

## Motivation

The independent question is Caceres' named converse primality criterion for
OEIS A308090 at every positive natural index. The formal surface consists only
of the OEIS definition and the single resolved Conjecture sentence.

## Gap

Readings of 2026-09-16: the OEIS entry still marks the line Conjecture
(unsigned, entry dated 2019-05-11) with no proof line; the 2021 Mathar note
relates the sequence to A090585 except at n = 2 and is not a proof; OpenAlex
`"A308090"` 0 hits; Math.SE API 0 hits; GitHub code search in
google-deepmind/formal-conjectures 0 hits. The prime-divisor argument is
elementary; the named criterion itself was not found in these surfaces. A GPT Pro reading of arxiv.org, openalex.org and math.stackexchange.com by A-number and by the defining phrases also found no proof; that reading is reported by the selection seat and is ASSUMED-UNVERIFIED.
Historical openness beyond them is ASSUMED-UNVERIFIED.

Repository prior art at `origin/dev`: `git grep A308090` returned 0 files in
D5/Blueprint/Library/Problems. The frozen A000680 sibling
`D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.result` and the
A006472 lane (PR #8215) are different primality criteria. Pinned Mathlib has
`Nat.exists_prime_and_dvd`, `Nat.dvd_factorial`, and
`Nat.Prime.dvd_of_dvd_pow`, but no statement of this criterion. Numerics for
`1 ≤ n ≤ 600` found 108 equality hits and zero hits with composite `n+1`;
the hits through 30 are 4, 6, 10, 12, 16, 18, 22, 28, and 30.

Pre-registration: issue #8212 (2026-09-15T22:10:16Z).

The public theorem is bind-only under the `open-problem-resolution` admission
basis registered in issue #8212. After all local `have`s are inlined, every
step is an instantiation of pinned Mathlib declarations, a divisibility
composition, or normalization. There is no escape witness. Direct frozen
dependencies: none, Mathlib only. The definition and theorem are unbounded
symbolic content rather than bounded enumeration, a checker, numeric
reduction, or a certified instance, so `utility: none` applies.

## Route

1. The gcd equality makes `n+1` divide both `2^n+n!` and `3^n+n!`.
2. If `n+1` is not prime, choose a prime `q` dividing it. The divisor cannot
   equal `n+1`, so `q ≤ n` and therefore `q ∣ n!`.
3. Cancelling the factorial term gives `q ∣ 2^n` and `q ∣ 3^n`. Primality
   gives `q ∣ 2` and `q ∣ 3`, hence `q ∣ gcd(2,3)=1`, a contradiction.

## Falsifier

A positive natural `n` with `a n = n+1` and composite `n+1` would falsify the
theorem. Finite numerical agreement cannot establish the universal claim.

## Evidence

- Final Lean module: `D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.lean`; 55 lines and 2289 UTF-8 bytes. At the landed commit `git ls-files 'D5/S3/Arith/Congruence/*.lean' | wc -l` reports 46 Lean files in its immediate directory (limit 96).
- Profiled `lake env lean D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.lean`: exit 0 with zero warnings; wall time 6.933 seconds and cumulative type checking 13.4 milliseconds.
- `tools/scripts/agent/header-check.sh D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.lean`: exit 0.
- Final-source `#print axioms` for `a` and `result`: exit 0; `a` uses `[propext]` and `result` uses `[propext, Classical.choice, Quot.sound]`.
- Deleting the sole direct import `Mathlib.Data.Nat.Prime.Factorial`: exit 1.
- Numeric check of the final definition for every `1 ≤ n ≤ 600`: exit 0; 108 equality hits and zero composite exceptions.

## Triage

`theorem`; resolution `proved` for the unsigned OEIS Conjecture sentence at
every positive natural index. The Scribe theorem node carries the matching
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

Historical openness beyond the OEIS, 2021 Mathar note, OpenAlex, Math.SE, and
GitHub code-search surfaces described above is unverified. No exhaustive
novelty or priority claim is made.
