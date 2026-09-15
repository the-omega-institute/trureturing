---
slug: oeis-a339669-odd-lucas-square-fibonacci-divisors
bibkey: lagneau2020a339669
doi: null
url: https://oeis.org/A339669
triage: theorem
motivation_gids:
  - D5/S1/Scale/Lucas
  - D5/S1/Scale/Fibonacci
  - D5/S0/Carrier/Conj
  - D5/S0/Carrier/Norm
  - D5/S0/Carrier/Ring
---

# Fibonacci Divisors of an Odd-Index Lucas Square Plus One

## Problem

OEIS A339669, NAME (verbatim):

> Number of Fibonacci divisors of Lucas(n)^2 + 1.

COMMENTS (verbatim):

> Particular attention must be paid to the regularity properties of the number of divisors of
> Lucas(n)^2 + 1 observed for n < 156, when a(n) = 1 or 2. From this observation, we propose two
> conjectures verified for n < 156.

> Conjecture 1: a(6*n+3) = 1.

> Conjecture 2: a(6*n+1) = a(6*n+5) = 2.

The count is of distinct divisor values, not of indices. The entry's own EXAMPLE line settles
this (verbatim):

> a(8) = 5 because the divisors of Lucas(8)^2 + 1 = 47^2 + 1 = 2210 are {1, 2, 5, 10, 13, 17,
> 26, 34, 65, 85, 130, 170, 221, 442, 1105, 2210} with 5 Fibonacci divisors: 1, 2, 5, 13 and 34.

The value 1 appears once although `F_1` and `F_2` are both 1. The same line shows why the
conjectures are confined to odd indices: at the even index 8 the count is 5, not 1 or 2.

Both indices `6n+1`, `6n+3` and `6n+5` are odd, so both conjectures are consequences of one
statement about odd indices:

> For every odd `n`, the set of Fibonacci divisors of `L_n^2 + 1` is `{1}` when `3` divides `n`
> and `{1, 2}` otherwise.

## Motivation

The frozen golden-integer layer already carries the two identities this needs. `D5/S1/Scale/Lucas`
defines `goldenLucas n` as the algebraic trace of `phi^n` and proves the discriminant identity
`L_n^2 - 5 * F_n^2 = 4 * (-1)^n`; `D5/S0/Carrier/Conj` and `D5/S0/Carrier/Norm` give the trace
and norm in integral coordinates, and `D5/S0/Carrier/Ring` gives the coordinate formulas for
products. The odd-index tripling identity below is obtained from those, not assumed.

## Gap

- The repository has no frozen statement about Fibonacci divisors of `L_n^2 + 1`, and none about
  `fib (3n) = fib n * (L_n^2 + 1)`. A search by mathematical object rather than by sequence
  identifier found the frozen discriminant and coordinate identities but no divisor statement.
- A Lean module proving the odd-index classification exists and compiles, but is **refused
  admission** under the per-declaration bind-only prohibition: every one of its declarations is
  obtained from frozen prerequisites and pinned Mathlib by instantiation, projection,
  recombination and normalization. Two independent read-only judgement seats reached that
  verdict separately and reported `escape_witness: none`, `admission_basis: none`. The second
  was asked to argue both sides of the two strongest declarations before deciding, and declined
  to manufacture a witness by restating the result.
- So the gap here is not the mathematics. It is that this result, as proved, cannot become a
  frozen node: the prohibition classifies a derivation relative to existing prerequisites and
  contains no exemption for settling an open conjecture.

## Route

The classification follows four steps, each stated for odd `n`.

1. Tripling. In the golden ring, the second coordinate of a cube satisfies
   `(x^3).b = x.b * (trace x ^ 2 - norm x)`. At `x = phi^n` the frozen identities
   `golden_phi_pow_b_eq_fib_index` and `norm_phi_pow` turn this into
   `fib (3n) = fib n * (L_n^2 + 1)` when `n` is odd, the sign of the norm being `-1` exactly
   there.
2. Coprimality with the index. For odd `n` put `M = L_n^2 + 1`. The discriminant gives
   `M + 3 = 5 * F_n^2`, so every common divisor of `F_n` and `M` divides 3; applying
   `fib gcd` at indices `n` and 4 gives `gcd (F_n, 3) = 1`, hence `gcd (F_n, M) = 1`. If
   `F_k` divides `M` then `F_(gcd (k, n)) = 1`, so `gcd (k, n) <= 2`, and since that gcd
   divides the odd `n` it equals 1.
3. The divisor bound. From step 1, `fib k` divides `fib (3n)`; with `gcd k n = 1` the strong
   divisibility property `fib (gcd m n) = gcd (fib m) (fib n)` forces `gcd k (3n)` to divide 3,
   hence `fib k` divides `fib 3 = 2`.
4. Parity. Reducing the same discriminant consequence `M + 3 = 5 * F_n^2` modulo 2 shows `2` divides `L_n^2 + 1` exactly when `2` does not divide `F_n`, which
   by the same strong divisibility property happens exactly when `3` does not divide `n`.

Steps 1 to 4 give the divisor set, and the two conjectures follow by taking cardinalities at
`n = 6t + 3`, `6t + 1` and `6t + 5`.

## Falsifier

A counterexample to the classification is an odd `n` whose Fibonacci-divisor set differs from
`{1}` when `3` divides `n`, or from `{1, 2}` otherwise. A counterexample to either numbered
conjecture is an odd index whose distinct-divisor count differs from the stated value. A
counterexample to the odd-index tripling identity would invalidate that step of the proof
route, without by itself settling the classification.

## Evidence

The Lean module compiles. On a full build of the tree it reports
`Built D5.S3.Arith.Congruence.OddLucasSquareFibonacciDivisors (49s)` and
`Build completed successfully (13305 jobs)`, and `#print axioms` on the two conjecture theorems
and on the divisor-set theorem each reports `[propext, Classical.choice, Quot.sound]`, with no
occurrence of `sorryAx` anywhere in the build log. That is a machine-checked proof; it is not a
frozen node, and this entry does not treat it as one.

The three smallest odd cases agree by hand: `L_1 = 1` gives 2, whose Fibonacci divisors are
`{1, 2}`; `L_3 = 4` gives 17, whose only Fibonacci divisor is 1; `L_5 = 11` gives
`122 = 2 * 61`, with Fibonacci divisors `{1, 2}`. The published DATA line, read on the same
date, begins `2,2,3,1,3,2,3,2,5,1,5,2,4,2,5,1,...` at offset 0, so its odd-index entries are
`a(1)=2, a(3)=1, a(5)=2, a(7)=2, a(9)=1, a(11)=2, a(13)=2, a(15)=1`, matching the
classification on those eight indices. The OEIS entry reports the conjectures as verified for
`n < 156`; that range was not recomputed here.

The current OEIS entry was read directly on 2026-09-14 through `oeis.org/search?q=id:A339669`.
Both numbered statements are still labelled conjectures there and no proof is linked.

## Triage

`theorem`. The mathematics is settled by the route above and machine-checked. This derivation
was refused admission under the per-declaration bind-only prohibition. This entry records the
mathematical result and that disposition; the module is not a frozen node.

## ASSUMED-UNVERIFIED

- The Lean module is not frozen and is not part of any delivery. Its compilation and axiom
  closure were observed on one tree at one revision; nothing in this entry depends on it being
  admitted later.
- The judgement that every declaration is bind-only is a review verdict, not a machine
  classification. The relevant guard is soft: the three required checks do not read proof shape.
- The `n < 156` verification quoted from OEIS was not reproduced here, and the hand checks above
  cover only `n = 1, 3, 5`.
- Whether the two conjectures have been proved elsewhere since the entry's last revision was
  checked only against the OEIS entry itself on the date given, not against the wider
  literature.
