---
slug: oeis-a386381-divisor-propagation
bibkey: kurkov2025a386381
doi: null
url: https://oeis.org/A386381/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.result
---

# All-divisor propagation for the modified Entringer diagonal

## Problem

OEIS A386381, revision 27, Conjecture 1 states:

> if d is a divisor of a(k), then d is also a divisor of a(m*d + k) where m is any natural number. In particular, a(k) is a divisor of a(m*a(k) + k) for any k >= 0 where m is any natural number.

Here `a(n)=T(n,n)` for A386363, revision 24. Its left boundary is
`T(0,0)=1`, `T(n,0)=0` for positive n; its first column is
`T(n,1)=T(n-1,n-1)`; its update for `2<=k<=n` is
`T(n,k)=T(n,k-1)+(n-2)*T(n-1,n-k)`.

The Lean theorem quantifies over all nonnegative k,m and positive integer
d, with no primality or finite cutoff. Conversion of d to a natural is
restricted to the sequence index. The particular assertion uses the
proved positivity of every a(k). Index zero, m=0 and d=1 are included.

## Motivation

This is the entire first source conjecture. The source's second conjecture
and its assertion about A060818 are excluded. Preregistration is
[#31218](https://github.com/the-omega-institute/trureturing/issues/31218),
Tier 1, settlement kind proof. The intended admission basis is
`open-problem-resolution`; no priority claim follows from a Lean proof.

## Gap

The source and bounded literature scope are in
[the Library note](../Library/RecurrenceComposition/kurkov2025a386381.md).
No earlier full supplier was found in that scope. Global novelty and
priority remain ASSUMED-UNVERIFIED. Freeze and independent final-byte
source/proof-shape review are separate from mathematical compilation.

## Route

Anchored reflected discrete summation constructs rational polynomials.
Repeated summation of one yields degree-j integer-valued polynomials.
The earlier all-integer Newton theorem gives a denominator bound of j!.
The explicit row expansion multiplies the j-th summand by the falling
factorial, a multiple of j!, so each complete row polynomial has integer
coefficients before any modular reduction.

Only the interior row positions are identified with source triangle
entries. The final source update adds zero, identifying the diagonal with
the last interior evaluation. Integer-coefficient evaluation is periodic
modulo d. Equality at the anchor and equality of backward differences,
propagated in both integer directions, prove the pointwise row relation.
Its diagonal specialization is
`a(n+d)=a(d+1)*a(n)` in `ZMod d` for positive n,d. Iteration propagates
divisibility; at k=0, d divides one and therefore equals one.

## Falsifier

A positive integer d and nonnegative k,m satisfying the source premise
and violating its conclusion would refute the conjecture. An alternate
triangle, a changed initial value, or failure of whole-sequence period d
would not be such a counterexample: the proof uses a multiplicative shift.

## Evidence

The canonical theorem is
`D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.result`.
Its exact Lean statement contains both the universal integer-modulus
assertion and the source's particular consequence. The corresponding
Blueprint explains the recurrence, interior restriction and denominator
cancellation. Compilation, scoped report and source-bound Reg evidence
are judged by the canonical producers; this dossier is not a check receipt
or a freeze certificate.

## Triage

The proof's structural consequence is the stronger multiplicative shift
congruence for all positive n,d. Whole-sequence period d is not needed.
The universal divisor conclusion includes composite moduli and prime
powers without inversion or a prime-power reduction. Generalizations to
other row weights and the two other OEIS assertions remain unproved here.

## ASSUMED-UNVERIFIED

Global novelty, publication priority, and completeness of the bounded
literature search remain ASSUMED-UNVERIFIED. The cited source and inspected
search scope do not establish exhaustive absence of an earlier proof or an
equivalent result. No claim is made beyond the complete first conjecture
stated above; Conjecture 2 and the A060818 assertion remain excluded.
