---
slug: oeis-a322327-schulte-exponent-product-omega-power-multiplicative
bibkey: schulte2018a322327
doi: null
url: https://oeis.org/A322327
triage: theorem
motivation_gids:
  - D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative
---

# Schulte's exponent-product multiplicativity conjecture

## Problem

OEIS A322327, NAME (`%N`, verbatim):

> a(n) = A005361(n) * A034444(n).

OFFSET (`%O`, verbatim):

> 1,2

AUTHOR (`%A`, verbatim):

> _Werner Schulte_, Dec 03 2018

COMMENT (`%C`, verbatim):

> Conjecture: Let k be some fixed integer and a_k(n) = A005361(n) * k^A001221(n) for n > 0 with 0^0 = 1. Then a_k(n) is multiplicative with a_k(p^e) = k*e for prime p and e > 0. For k = 0 see A000007 (offset 1), for k = 1 see A005361, for k = 2 see this sequence, for k = 3 see A226602 (offset 1), and for k = 4 see A322328.

A005361, NAME (`%N`, verbatim):

> Product of exponents of prime factorization of n.

A001221, NAME (`%N`, verbatim):

> Number of distinct primes dividing n (also called omega(n)).

For every integer `k`, define
`a_k(n) = (product over prime divisors p of n of v_p(n)) * k^omega(n)`,
where `v_p(n)` is the exponent of `p` in the prime factorization and the
empty product is one. The full-quantifier reading asks that for all positive
naturals `m,n` with `gcd(m,n)=1`, `a_k(mn)=a_k(m)*a_k(n)`, and that for all
natural primes `p` and positive exponents `e`, `a_k(p^e)=k*e`. Lean's
convention gives `0^0=1`. The formal theorem establishes the same equations
for all natural `m,n` satisfying coprimality, which includes the stated
positive domain.

The scope wall contains only those two assertions in the conjecture sentence
for every integer `k`. The trailing correspondences with A000007, A005361,
A322327, A226602, and A322328 are not claimed.

## Motivation

The independent question is Schulte's named OEIS conjecture about the entire
integer-parameter family, not one finite instance. `question_answered` is the
A322327 `%C` conjecture sentence quoted above and preregistered in issue #8138.
The public result is unbounded and symbolic.

`proof_shape: bind-only`; `escape_witness: null`;
`admission_basis: open-problem-resolution`. The proof directly specializes
and normalizes pinned Mathlib results, with every auxiliary step kept as a
local `have` inside `result` and no helper theorem declaration. The admission
basis is the external named open-problem settlement exception.

`computational_content.kind: none`: neither the definition nor the theorem is
a bounded enumeration, checker, numerical reduction, or certified finite
instance. The finite numerical check is only a falsification attempt. Other
computational-utility fields are `not-applicable(kind=none)`.

## Gap

Readings of 2026-09-16: the OEIS entry still marks the line Conjecture (last edited 2026-04-09) with no proof line; OpenAlex `"A322327"` 0 hits; Math.SE API 0 hits; arXiv was not searched (no API response). Historical openness beyond these surfaces is ASSUMED-UNVERIFIED.

Pre-registration issue #8138 (created 2026-09-15T17:24:55Z) precedes the first proof attempt (2026-09-15T17:26:11Z)

Repository prior art at `origin/dev = 9740a07f66b6f1fe7b9fe634c88c1c9d115e22ff`:
`git grep -E 'A322327|A005361'` has 0 hits in D5, Library, and Problems
(exit 1). The repository search found no product-of-exponents definition.
The closest named result is `prime_exponent_product_formula` in
`D5/S3/Factorization/ExponentCoordinates/PrimeExponentBijection.lean`; it
reconstructs a number as a product of prime powers and does not define the
product of factorization exponents or state this target.

Pinned Mathlib contains `Nat.factorization_mul`, `Nat.primeFactors_mul`,
`Nat.Coprime.disjoint_primeFactors`, `cardDistinctFactors_mul`,
`Nat.Prime.factorization_pow`, and `cardDistinctFactors_apply_prime_pow`.
It contains no A005361 definition and no statement of the target.
`dominating_theorem_search: not-found-in-searched-scope` for the complete
conjecture in the repository roots and pinned Mathlib; the component results
are reused directly.

Numerical readings cover every integer `k` in `[-3, 4]`, all positive
coprime ordered pairs `m,n <= 200`, and all 46 primes `p <= 200` with
`1 <= e <= 8`. There are zero exceptions among 195704 multiplicativity
checks and 2944 prime-power checks. The check also reports `0^0=1`.
Finite agreement does not prove either universal assertion.

## Route

1. For coprime `m,n`, split the factorization-exponent product across the
   disjoint prime-factor sets, split `omega(mn)` additively, and rearrange the
   integer products to prove `a_k(mn)=a_k(m)*a_k(n)`.
2. For prime `p` and positive `e`, reduce the prime-divisor set of `p^e` to
   `{p}`, evaluate its factorization exponent as `e`, evaluate omega as one,
   and commute the two integer factors to obtain `k*e`.

## Falsifier

An integer `k` and positive coprime naturals `m,n` violating the displayed
multiplicativity equation would refute the first assertion. A prime `p` and
positive exponent `e` with `a_k(p^e) != k*e` would refute the second. A
mismatch between the formal definition and A005361 times `k^A001221` would
invalidate the bridge to the OEIS sentence. Finite numerical agreement cannot
exclude these universal failures.

## Evidence

The final module is
`D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.lean`, with the
public definition `a` and public theorem `result`, no private theorem
declarations, 50 lines, and 2170 bytes. Its directory contains 47 Lean files.

- `lake env lean D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.lean`
  exits 0.
- `tools/scripts/agent/header-check.sh D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.lean`
  exits 0.
- The scratch axiom query exits 0. Both `a` and `result` have exactly
  `[propext, Classical.choice, Quot.sound]`.
- The profiled scratch check exits 0, with 12.12 seconds wall time and 1.43 ms
  cumulative type checking.
- The exact-integer numerical check exits 0.
- Deleting the sole direct import,
  `Mathlib.NumberTheory.ArithmeticFunction.Misc`, gives Lean exit 1.

| Deleted import | Exit |
| --- | --- |
| `Mathlib.NumberTheory.ArithmeticFunction.Misc` | 1 |

## Triage

`theorem`; resolution `proved` for both assertions in the quoted conjecture
sentence for every integer parameter `k`.

## ASSUMED-UNVERIFIED

The literature check performed on 2026-09-16 read the OEIS conjecture status
and last-edit marker, queried OpenAlex for `"A322327"` with 0 hits, queried the
Math.SE API with 0 hits, and received no arXiv API response, so arXiv was not
searched. Only historical openness beyond those searched surfaces is
`ASSUMED-UNVERIFIED`.
