---
slug: oeis-a000680-schulte-half-factorial-prime-criterion
bibkey: schulte2025a000680
doi: null
url: https://oeis.org/A000680
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion
---

# Schulte's A000680 half-factorial primality criterion

## Problem

OEIS A000680, NAME (`%N`, verbatim):

> a(n) = (2n)!/2^n.

The settled COMMENT (`%C`, verbatim) is:

> Conjecture: For n > 0 (a(n) + 2^n) is a multiple of (2*n + 1) if and only if (2*n + 1) is a prime number. - _Werner Schulte_, Oct 05 2025

The offset is `%O 0,3`, and the AUTHOR line (`%A`, verbatim) is:

> _N. J. A. Sloane_

The full-quantifier reading is: for every `n : Nat`, if `0 < n`, then
`(2 * n + 1) ∣ a n + 2 ^ n` if and only if `(2 * n + 1).Prime`. The scope wall
is exactly this biconditional for every positive natural `n`; no additional
sequence values, implications, or historical claims are included.

## Motivation

The independent question is Schulte's named primality characterization of
OEIS A000680 for every positive natural index. It is registered as an external
open problem under pre-registration issue #8173. The formal result keeps the
OEIS definition and the single Conjecture sentence as its public surface.

## Gap

Readings of 2026-09-16: the OEIS entry still marks the line Conjecture (added
2025-10-05) with no proof line; OpenAlex `"A000680"` returns 33 hits, none
about this criterion; Math.SE API 24 hits, none about it; arXiv was not
searched (no API response). Wilson's theorem and the odd-composite factorial
divisibility are textbook facts; the named criterion itself was not found in
these surfaces. Historical openness beyond them is ASSUMED-UNVERIFIED.

Repository prior art at `origin/dev`: `git grep A000680` returned 0 hits.
`ZMod.wilsons_lemma` is used by 2 D5 modules. The frozen
`D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime`
supplies the odd-composite factorial step and is REUSED; its direct frozen
dependency is GID
`D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime`,
declaration statement_id
`sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600`,
with module pin
`sha256:0b53e5405adaa92296c5ed5a39e491fdddcc8d7f599adef8aa1f170222f074d4`.
That theorem does not by itself state the criterion because it only gives
factorial divisibility for the odd-composite branch, not the equivalence with
the A000680 expression.

Pinned Mathlib contains `ZMod.wilsons_lemma`,
`ZMod.pow_card_sub_one_eq_one`, `Nat.factorial_eq_mul_doubleFactorial`, and
`Nat.doubleFactorial_two_mul`; no statement of the criterion was found.
Numerics for `1 ≤ n ≤ 600` checked both directions with zero exceptions; there
are 196 primes `2n+1` in the range.

Pre-registration: issue #8173 (2026-09-15T19:06:58Z).

The public theorem is bind-only under the `open-problem-resolution` admission
basis. The proof has no escape witness and no helper theorem declarations. Its
direct frozen dependency is the LaymanOddPowerFactorialResidue declaration
listed above; all remaining steps instantiate pinned Mathlib results and
normalize their consequences.

## Route

1. Use `2^n * a(n) = (2n)!` from the exact natural-number quotient.
2. Multiply the divisibility statement by the unit `2^n` modulo `2n+1`.
3. In the prime direction, use Wilson's theorem for `(2n)!` and Fermat's
   theorem for `2^(2n)`.
4. In the composite direction, use the frozen odd-composite factorial
   divisibility and cancel the factorial term, leaving a coprime power.

## Falsifier

A positive natural `n` for which the divisibility and primality sides differ
would falsify the theorem. A composite `2n+1` satisfying the divisibility, or
a prime `2n+1` failing it, is a direct counterexample. Finite numerical
agreement cannot establish the universal claim.

## Evidence

- Final Lean module: `D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.lean`; 96 lines and 4320 UTF-8 bytes; its directory contains 44 Lean files.
- `lake env lean D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.lean`: exit 0.
- `tools/scripts/agent/header-check.sh D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.lean`: exit 0.
- Final-source `#print axioms` for `a` and `result`: exit 0; `a` uses `[propext]` and `result` uses `[propext, Classical.choice, Quot.sound]`.
- Deleting `Mathlib.Data.Nat.Factorial.DoubleFactorial` from the direct imports: exit 1; deleting the frozen `LaymanOddPowerFactorialResidue` import: exit 1.
- Numeric check of the final definition for every `1 ≤ n ≤ 600`: exit 0; both directions, 196 prime cases, zero exceptions.

## Triage

`theorem`; resolution `proved` for the OEIS Conjecture sentence at every
positive natural index. The Scribe theorem node carries the matching
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

Historical openness beyond the OEIS, OpenAlex, and Math.SE surfaces described
above is unverified. The arXiv surface was not searched because its API gave no
response. No exhaustive novelty or priority claim is made.
