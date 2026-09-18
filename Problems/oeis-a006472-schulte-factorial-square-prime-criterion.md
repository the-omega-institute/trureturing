---
slug: oeis-a006472-schulte-factorial-square-prime-criterion
bibkey: schulte2020a006472
doi: null
url: https://oeis.org/A006472
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion
---

# Schulte's factorial-square primality criterion

## Problem

OEIS A006472, NAME (`%N`, verbatim):

> a(n) = n!*(n-1)!/2^(n-1).

The offset is `%O 1,3`. The settled COMMENT line (`%C`, verbatim) is:

> Conjecture: For n > 1, n divides 2*a(n-1) + 4 if and only if n is prime. - _Werner Schulte_, Oct 04 2020

The full-quantifier reading is: define, for every natural `m`,
`a(m) = m!*(m-1)!/2^(m-1)` using natural-number division; then for every
natural `n` with `2 <= n`, `n` divides `2*a(n-1)+4` if and only if `n` is
prime. The denominator divides the factorial product for every `m >= 1`, so
all sequence values used by the criterion are exact quotients.

Only the quoted Conjecture sentence is settled, as a biconditional for every
natural `n >= 2`. No other OEIS comment, formula, or stronger composite
divisibility statement is claimed.

## Motivation

The criterion combines an exact quotient of two neighboring factorials with a
single divisibility test. For primes, Wilson's theorem controls `(n-1)!` and
Fermat's theorem controls the removed power of two. For composites, the same
quotient has enough factorial content to force a contradiction, apart from the
small cases that are checked directly.

## Gap

Readings of 2026-09-16: the OEIS entry still marks the line Conjecture (added
2020-10-04) with no proof line; OpenAlex `"A006472"` 8 hits, none about this
criterion; Math.SE API 0 hits; arXiv was not searched (no API response).
Wilson's theorem and the composite-factorial divisibility are textbook facts;
the named criterion itself was not found in these surfaces. Historical
openness beyond them is ASSUMED-UNVERIFIED.

Repository prior art at `origin/dev` = `6c7f849f03` (paths `D5`, `Blueprint`,
`Library`, `Problems`; `Golden/**` excluded): `git grep A006472` returned 0 files;
`wilsons_lemma` matched 6 files, `factorial_dvd_triangular` 6 files (7 tree-wide),
and `multiplicity_factorial` 1 file (2 tree-wide). None states the criterion. The
closest frozen settlement is the A000680 sibling
`D5/S3/Arith/Congruence/SchulteHalfFactorialPrimeCriterion.result`
((2n+1) ∣ (2n)!/2^n + 2^n ⟺ 2n+1 prime), a different criterion that shares only
the Wilson/Fermat prime branch and the Layman odd-composite step. The
frozen theorem
`D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.factorial_dvd_triangular_of_not_odd_prime`
supplies the odd-composite factorial step and is reused. Its declaration
`statement_id` is
`sha256:e66be6c11321ef2a8bb90c32fb4a9755ab1468d5aece54699035c65784793600`;
the module state pin is
`sha256:0b53e5405adaa92296c5ed5a39e491fdddcc8d7f599adef8aa1f170222f074d4`.

Pinned Mathlib contains `ZMod.wilsons_lemma`,
`ZMod.pow_card_sub_one_eq_one`, `Nat.factorial_eq_mul_doubleFactorial`, and
`Nat.doubleFactorial_two_mul`, but no statement of Schulte's criterion was
found in the searched scope. Exact evaluation for every `2 <= n <= 600`
finds zero exceptions in either direction. Exact division has zero failures
for every `1 <= m <= 599`; the initial values are `a(1)=1`, `a(2)=1`, and
`a(3)=3`.

Pre-registration: issue #8189 (2026-09-15T20:09:17Z).

## Route

1. Splitting each factorial at its even factors proves
   `2^(m-1) | m!*(m-1)!` for every `m >= 1`, so multiplication recovers the
   numerator from `a(m)`.
2. For odd prime `n`, the scale `2^(n-2)` is a unit modulo `n`. Wilson gives
   `(n-1)! = -1`, factorial recursion gives `(n-2)! = 1`, and Fermat gives
   `2^n = 2` in `ZMod n`. Cancelling the scale proves the forward divisibility.
3. For composite `n >= 9`, the private theorem `composite_dvd_a` proves
   `n | a(n-1)`. If `n` is even, write `n=2k`; double-factorial identities
   expose the quotient, and a parity split on `k` supplies `k` and the extra
   factor 2 by factorial divisibility or coprime cancellation. If `n` is odd,
   the reused triangular-factorial theorem supplies `n | (n-1)!`, and
   coprimality with `2^(n-2)` cancels the exact-division scale. The finite
   branch handles `n < 9`; in particular `n=4` and `n=8` require direct
   treatment because they do not divide `a(n-1)`.
4. Thus a composite satisfying the criterion would have `n | 4`, contradicting
   `n >= 9`; the normalized finite branch closes the remaining values.

The public theorem has `proof_shape: content` and
`admission_basis: escape-witness`. The witness is the private theorem
`composite_dvd_a {n} (hn : 9 <= n) (hnprime : not n.Prime) : n | a(n-1)`.
It passes the four content tests: (i) `result` directly applies the private
theorem, so its declaration is in the elaborated transitive dependency closure;
(ii) its parity split, double-factorial quotient analysis, coprimality, and
factorial-divisibility construction do not follow by instantiation,
projection, or normalization of the searched frozen and pinned declarations;
(iii) it is a conditional one-way composite divisibility theorem, not a
definitionally equivalent restatement of the primality biconditional; and
(iv) it lies on the live derivation path from assumed criterion divisibility to
`n | 4`. Removing it leaves the unbounded composite branch unproved. The direct
frozen dependency is the Layman theorem and declaration identity recorded in
the Gap section. All other proof steps are local `have` terms.

`utility: none` applies to all declarations: the sequence definition, private
divisibility theorem, and unbounded primality criterion are symbolic
mathematics, not bounded enumeration, checker infrastructure, numeric
reduction, or a certified finite instance.

## Falsifier

A natural `n >= 2` for which exactly one of `n | 2*a(n-1)+4` and `n.Prime`
holds would refute the result. Failure of
`2^(m-1) | m!*(m-1)!` for any `m >= 1` would refute the exact-quotient step.
The stronger statement that every composite `n >= 4` divides `a(n-1)` is not
claimed: exact evaluation refutes it at `n=4` and `n=8`.

## Evidence

- `lake env lean D5/S3/Arith/Congruence/SchulteFactorialSquarePrimeCriterion.lean`:
  exit 0 with zero warnings. The final module has 273 lines; its immediate
  directory has 45 Lean files. Its declaration surface is public `a`, private
  `composite_dvd_a`, and public `result`. A token search for `sorry`, `admit`,
  `axiom`, and `native_decide` exits 1 with no matches.
- `tools/scripts/agent/header-check.sh` on the final module: exit 0;
  `generality: I` is compliant.
- Scratch `#print axioms` audit: exit 0. The closures are `[propext]` for `a`
  and `[propext, Classical.choice, Quot.sound]` for both private
  `composite_dvd_a` and public `result`.
- Deleting the direct import
  `D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue` and compiling exits 1,
  with the frozen theorem unknown. Deleting
  `Mathlib.Data.Nat.Factorial.DoubleFactorial` and compiling exits 1, with the
  double-factorial notation and identities unavailable. Both imports are
  load-bearing.
- Lean evaluation of the final definition for `1 <= m <= 599` and
  `2 <= n <= 600`: exit 0; exact-division failures `[]`, criterion exceptions
  `[]`, and seeds `[a(1),a(2),a(3)] = [1,1,3]`.
- Warm-cache single-file profiling: exit 0; 3.91 seconds wall, 315 milliseconds
  type checking, and 1.18 seconds import time on Lean 4.33.0 for arm64 macOS.

## Triage

`theorem`; resolution `proved` for the quoted Conjecture sentence and its full
natural-number range `n >= 2`.

## ASSUMED-UNVERIFIED

The verbatim OEIS source, the 2026-09-16 external search readings, the
historical `origin/dev` prior-art counts, and the pre-registration chronology
are ASSUMED-UNVERIFIED. arXiv was not searched because no API response was
available. Historical openness outside the listed surfaces remains unverified.
No exhaustive literature search or mathematical-priority claim is made. The
stronger composite divisibility statement for `n=4` or `n=8` is explicitly
excluded.
