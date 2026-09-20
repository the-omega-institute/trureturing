---
slug: oeis-a000071-bala-strong-divisibility
bibkey: bala2022a000071
doi: null
url: https://oeis.org/A000071
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LucasEvenDescent
  - D5/S1/Recurrence/LucasCompanion
---

# Bala's Fibonacci-power strong divisibility conjecture

## Problem

OEIS A000071 has `a(t)=F_t-1`, with Fibonacci initial values F_0=0,
F_1=1. Peter Bala's COMMENTS entry of Dec 05 2022 states:

> Conjecture: for k a positive odd integer, the sequence {a(k^n): n >= 1} is a strong divisibility sequence; that is, for n, m >= 1, gcd(a(k^n), a(k^m)) = a(k^gcd(n,m)).

The exact formal statement is:

```lean
theorem result (k n m : ℕ) (hk : Odd k) (hn : 0 < n) (hm : 0 < m) :
    Nat.gcd (Nat.fib (k ^ n) - 1) (Nat.fib (k ^ m) - 1) =
      Nat.fib (k ^ Nat.gcd n m) - 1
```

Oddness of a natural k supplies its positivity. The source's k=1 and
every pair of positive indices are included; there is no cutoff,
changed offset, or conditional prime restriction.

## Motivation

Subtracting one destroys the ordinary Fibonacci strong-divisibility
identity at arbitrary indices. Restricting the indices to powers of
one odd base recovers an exact gcd identity. Matrix return times expose
the common relation needed to compare all these indices.

## Gap

The missing source-specific bridge was the equivalence, for every prime
p, positive e and odd t, between F_t=1 modulo p^e and Q^t being Q or
Q inverse, where Q=[[1,1],[1,0]]. This is implemented inside `result`.
It is false for arbitrary composite moduli: modulo 6, t=7 gives
F_7=13=1, but Q^7=[[3,1],[1,2]] is neither of the two return matrices.

Issue #9152 preregisters this representation. Issue #7980 remains closed
with its missing Lucas-gcd prerequisite and no resolution credit. A fresh
all-state A000071 issue search in this flight returned #9152, #7980 and
the two standing research programme issues, with no additional exact-target
owner; the corresponding all-state PR search returned no results.
The bounded source and literature findings and their attribution
limits are in the Library note.

## Route

For a prime power modulus, the frozen Lucas recurrence identifies
lucasU 1 (-1) at natural indices with the cast Fibonacci sequence.
The frozen power-shape and determinant theorems give, when t is odd
and F_t=1, Q^t=[[x+1,1],[1,x]] and x(x+1)=0. For the natural
representative a of x, p^e divides a(a+1). Splitting on p dividing a
and using coprimality with the other factor puts the whole prime power
in one factor. Therefore x=0 or x=-1. Conversely, either return matrix
has lower-left entry one. No division by 2 or 5 occurs.

On sets of matrix units, use S={Q,Q inverse} and the single map T that
takes the image under kth powers. Mathlib `pow_iterate` and
`Set.image_iterate_eq` identify the r-th iterate. Equality of inverse
pairs is equivalent to Q^(k^r)=Q or Q inverse, even if the two elements
coincide. Positivity of Fibonacci values justifies casting natural
subtraction, giving p^e dividing F_(k^r)-1 iff `IsPeriodicPt T r S`.

`Function.IsPeriodicPt.gcd` gives forward gcd divisibility and
`Function.IsPeriodicPt.trans_dvd` gives reverse divisibility.
`Nat.dvd_iff_prime_pow_dvd_dvd` and antisymmetry reconstruct equality.
The divisor p^0=1 is handled separately. The argument also handles r=0
internally; the public signature retains the source's positive n,m.

The proposed `proof_shape` is `content`, with the live prime-power
matrix-return equivalence as the substantive local assertion; independent
admission review remains required. `admission_basis` is
`open-problem-resolution`, tied to the exact preregistered external
conjecture. `utility: none`: this is an unbounded symbolic theorem.
There is exactly one new public theorem and no standalone helper declarations.

The direct frozen suppliers are
`D5/S1/Recurrence/LucasEvenDescent` (statement ID
`ec1893c203633ded2c1b46612bb05f8cca1555e38d0934e23aa58e23401c5043`)
and `D5/S1/Recurrence/LucasCompanion` (statement ID
`0b0605149efa20ae7641e1be71fc7f4d09631f787899ba3babdfbf160cb1e231`).
Mathlib is pinned at `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Falsifier

An odd positive k and positive n,m for which the two natural numbers in
the exact statement differ would refute the conjecture. The modulus-6
example refutes only a composite-modulus extension of the bridge, not
the conjecture. At k=1 every sequence value and both sides are zero.

## Evidence

The canonical targeted `make lean` build of
`D5.S1.Recurrence.BalaFibonacciPowerStrongDivisibility` exited 0.
The compiler's axiom closure for `result` is exactly `propext`,
`Classical.choice`, `Quot.sound`. The proof directly applies the frozen
recurrence, power shape and determinant, then the pinned Mathlib
iteration, periodicity and divisibility suppliers. It has no extra
formal premise, sorry, private axiom, or finite enumeration.

The native worker verified the source statement and supplier contracts.
Independent review, canonical Freeze, final required CI, ordinary merge
and completion audit remain caller-owned obligations; compilation does
not claim those outcomes or resolution credit.

## Triage

`theorem`, Tier 1, source year 2022: an externally published small
conjecture with no exact resolution found in the stated bounded searches.
The age of the source does not imply either difficulty or novelty.

## ASSUMED-UNVERIFIED

The earlier paper and external Lean search readings are supplied by the
caller and were not independently repeated in this implementation.
Openness outside the inspected sources and worldwide priority remain
unverified. No model-diversity or independent-priority claim is made.
The earlier scalar-polynomial alternative is uncompiled and unused;
no lower formalization cost has been established for it. This flight
does not supply the independent review or any final lifecycle credit.
