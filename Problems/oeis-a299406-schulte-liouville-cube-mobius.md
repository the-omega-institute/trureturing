---
slug: oeis-a299406-schulte-liouville-cube-mobius
bibkey: schulte2018a299406
doi: null
url: https://oeis.org/A299406
triage: theorem
motivation_gids:
  - D5/S3/Arith/SchulteLiouvilleCubeMobius
---

# Schulte's Liouville and cube-Möbius product formula

## Problem

OEIS A299406, NAME (`%N`, verbatim):

> Dirichlet g.f.: Sum_{n>0} a(n)/n^s = (zeta(s)*zeta(6*s))/(zeta(2*s)*zeta(3*s)).

FORMULA (`%F`, verbatim):

> Conjecture: a(n) = A008836(n) * A210826(n).

AUTHOR (`%A`, verbatim):

> _Werner Schulte_, Feb 20 2018

The offset (`%O`) is `1,1`. A008836, NAME (`%N`, verbatim):

> Liouville's function lambda(n) = (-1)^k, where k is number of primes dividing n (counted with multiplicity).

A210826, NAME (`%N`, verbatim):

> G.f.: Sum_{n>=1} a(n)*x^n/(1 - x^n) = Sum_{n>=1} x^(n^3).

Let `zeta` be the arithmetic function equal to one on positive inputs, `mu`
the Möbius function, and `⋆` Dirichlet convolution. For positive `k`,
`liftPow k f` has value `f(m)` at `m^k` and zero off exact k-th powers.
The total Lean definition uses the guard
`(Nat.floorRoot k n)^k = n`. Here `Nat.floorRoot` divides prime-factor
exponents by `k` using natural-number division; it returns zero if `k = 0`
or `n = 0`. This is the root for divisibility, not a real-root approximation.

The coefficient reading of `zeta(6s)` is `liftPow 6 zeta`, and that of
`1/zeta(ks)` is `liftPow k mu` for `k = 2, 3`. Hence set
`A = zeta ⋆ liftPow 6 zeta ⋆ liftPow 2 mu ⋆ liftPow 3 mu`.
The Lambert-series reading is
`sum_{d|n} B(d) = [n is a positive cube]`, where brackets are an indicator.
Möbius inversion gives `B = mu ⋆ liftPow 3 zeta`, representing A210826.
Both functions take integer values and vanish at zero.

The exact formal claim is
`forall n : Nat, 0 < n -> A n = ArithmeticFunction.liouville n * B n`.
Mathlib's `liouville_apply` identifies the named function with
`(-1 : Int) ^ Omega(n)` for positive `n`, matching A008836's `%N`.
Only the quoted A299406 `%F` line is settled under these coefficient
interpretations. Analytic convergence, analytic uniqueness of the series,
and other OEIS assertions are outside the claim. The hypothesis `0 < n`
excludes zero, as required by A299406's offset one.

## Motivation

The independent question is Schulte's published product conjecture, relating
three coefficient sequences for every positive natural index. It is the
first-tier external named small-conjecture target in preregistration issue
#8094 (created 2026-09-15T13:03:08Z), which precedes the first proof attempt
(2026-09-15T13:04:06Z).

`question_answered`: the A299406 `%F` line quoted above, preregistered in
#8094. `proof_shape: bind-only`; `escape_witness: null`;
`admission_basis: open-problem-resolution`. The conclusion is obtained from
pinned Mathlib multiplicativity and prime-power formulas by instantiation,
finite-sum rearrangement, and parity normalization. All auxiliary steps are
local `have`s inside `result`; there are no helper theorem declarations or
direct frozen repository dependencies. The admission basis is the external
open-problem settlement exception, with its literature premises explicitly
bounded below.

`computational_content.kind: none`: the three definitions specify unbounded
arithmetic functions and the theorem quantifies over all positive natural
indices. No bounded enumeration, checker, numerical reduction, or certified
finite instance is delivered. Other computational-utility fields are
`not-applicable(kind=none)`; the finite numerical scans only detect faults.

## Gap

Literature readings of 2026-09-15: OEIS still marks the A299406 `%F`
line as Conjecture, and A210826 has no corresponding confirmation. OpenAlex
for `A299406` returned 0 results; the Math.SE API returned 0;
formal-conjectures returned 0. The arXiv API returned HTTP 429 and was not
searched. No proof was found in those searched surfaces. These scoped
readings do not establish exhaustive historical openness or priority.

Repository prior art at `origin/dev = fe47b6c24b`: D5, Library, and
Problems contain no power lift and none of these three sequences. Mathlib's
`ArithmeticFunction.liouville` is already used by two frozen modules,
`PrimeWordAntipodeParityStepBridge` (`liouville_prime_word_product`: the
Liouville value of a product of prime words) and
`PrimeGoldenBigradedChronologicalSignature`
(`factor_parity_character_eq_liouville`); both concern parity characters of
prime words and neither states a Dirichlet-convolution identity, so they do
not cover this target. The frozen `LiouvilleParityHolomorphyCriterion`
concerns zeta holomorphy, not this coefficient identity. The SHA identifies
the search snapshot, not the implementation HEAD.

Pinned Mathlib provides arithmetic functions `zeta`, `mu`, `Omega`, and
`ArithmeticFunction.liouville`, multiplicative extensionality
`IsMultiplicative.eq_iff_eq_on_prime_powers`, and `Nat.floorRoot`.
No power lift or full target identity was found.
`dominating_theorem_search: not-found-in-searched-scope` for the complete
identity, in the repository roots and pinned Mathlib arithmetic-function
modules; the component declarations are reused directly.

Numerical readings: exact reproduction of the first 32
A299406 and 28 A210826 data values and no exception for `1 <= n <= 4000`.
An independent exact-integer check of the final definitions also
reports no exception through `n = 2000`.
These finite observations do not establish the universal theorem.

## Route

1. Use coprime power extraction and the exact-power guard to transfer
   multiplicativity to the power lifts. Dirichlet convolution then makes
   A and B multiplicative; Liouville is completely multiplicative.
2. On a prime power `p^e`, the lifted Möbius function is
   `[e = 0] - [e = k]`. Convolution with it subtracts a k-step shift.
   The lifted zeta value is `[k divides e]`.
3. Normalize the prime-power formulas. Both A and the pointwise product
   `liouville * B` have the six-periodic coefficient pattern
   `1, 1, 0, -1, -1, 0`, beginning at exponent zero.
4. Apply multiplicative extensionality to obtain the identity at every
   positive natural index.

## Falsifier

A positive natural `n` for which the stated convolution definitions violate
`A(n) = liouville(n) * B(n)` would refute the identity. A mismatch between
the coefficient interpretations and the quoted generating functions would
invalidate the correspondence with the OEIS claim. Bounded numerical
agreement alone cannot rule out either universal obligation.

## Evidence

The formal module is `D5/S3/Arith/SchulteLiouvilleCubeMobius.lean`, with public
definitions `liftPow`, `A`, `B` and the single public theorem `result`.

- Final single-file `lake env lean` exits 0 with zero warnings; measured
  wall time is 12.508076 seconds. The final module has 205 lines and 9156
  bytes; its containing directory has 46 Lean files.
- `tools/scripts/agent/header-check.sh` exits 0. The seven-line header has
  generality G, utility none, and a digest line of 95 characters, including
  its 81-character payload.
- A scratch copy of the final source with profiling and four axiom queries
  exits 0. Each of `liftPow`, `A`, `B`, and `result` has exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  or new axiom occurs in the final module.
- The scratch profile reports 2.65 seconds of cumulative kernel type
  checking and 25.312611 seconds wall time, including profiling output and
  the axiom queries. Measurements use Lean v4.33.0 on macOS 26.6.2 arm64
  with a warm cache. Peak resident memory was not measured.
- The exact-integer Python implementation of the final guarded lifts and
  convolution definitions exits 0. There are zero exceptions for
  `1 <= n <= 2000`; the first 32 A299406 and 28 A210826 values match the
  OEIS data exactly. The factorization-root guard agrees with direct
  power placement for lifts 2, 3, and 6 of both zeta and mu. This is finite
  fault detection, independent of the universal Lean proof.

Deleting each final direct import separately gives the following bare Lean
exit codes. No direct D5 or umbrella tactic import remains.

| Deleted import | Exit |
| --- | --- |
| `Mathlib.NumberTheory.ArithmeticFunction.Liouville` | 1 |
| `Mathlib.NumberTheory.ArithmeticFunction.Moebius` | 1 |
| `Mathlib.Data.Nat.Factorization.Root` | 1 |
| `Mathlib.Algebra.GCDMonoid.Nat` | 1 |

Scribe source selfchecks cover the four public declarations, matching binder
symbols, integer coercions, and grouped named functions; relations occur
outside `LatexGroup.Items`.

## Triage

`theorem`; resolution `proved` for the product formula at every positive
natural index under the stated coefficient interpretations.

## ASSUMED-UNVERIFIED

The external OEIS locators, search counts, preregistration chronology of
#8094, the `fe47b6c24b` repository-search reading, and the scan through
4000 were read on 2026-09-15 and are `ASSUMED-UNVERIFIED` here. The arXiv search was not performed (HTTP 429).
Historical openness outside the stated search surfaces and exhaustive
novelty or priority are unverified. The coefficient readings are the stated
interpretive bridge; the Lean theorem is the unbounded arithmetic identity.
