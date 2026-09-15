---
slug: oeis-a000040-detlefs-fibonacci-fermat-prime-characterization-refutation
bibkey: sloane2014a000040
doi: null
url: https://oeis.org/A000040
triage: theorem
motivation_gids:
  - D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation
---

# Refutation of Detlefs's A000040 Fibonacci-Fermat prime characterization

## Problem

OEIS A000040, NAME (verbatim):

> The prime numbers.

Gary Detlefs's FORMULA of May 25, 2014 (verbatim):

> Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014

His FORMULA of May 28, 2014 (verbatim):

> Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(3*n) mod 3*n = 8}. - _Gary Detlefs_, May 28 2014

For natural numbers, define
`fibTest(n) := (Fibonacci(n) mod n = 1) or
(Fibonacci(n) mod n = n-1)`, define
`fermatTest(n) := 2^(n-1) mod n = 1`, and define
`inDetlefsSet(n) := (n=5) or
(n!=5 and fibTest(n) and fermatTest(n))`. The literal refuted statement is
`claim := for every natural n, 0<n implies
(Prime(n) iff inDetlefsSet(n))`.

Only the May 25 characterization is claimed and refuted here. The May 28
variant is disclosed but not claimed, although 219781 also satisfies its
congruence. Detlefs's September 10, 2010 Wilson-type characterizations in the
same FORMULA block are not claimed or assessed.

## Motivation

The May 25 formula identifies the prime numbers exactly with five and the
non-five values satisfying both a Fibonacci residue test and a Fermat residue
test. A composite value satisfying both tests refutes the substantive reverse
direction of the universal biconditional. The literal statement also fails at
the degenerate boundary `n=2`, where a prime lies outside the proposed set.

## Gap

Searches recorded on September 14, 2026 checked the current A000040 text and
its newest ten visible revisions. Both 2014 formulas remain labelled
"Conjecture" without a refutation note. Older OEIS history was
anonymous-locked and is `ASSUMED-UNVERIFIED`.

The checked arXiv, OpenAlex, MathOverflow, and GitHub surfaces contain no
proof or refutation of the May 25 characterization. OEIS search for
`seq:219781,252601,399001` returned no result. These bounded searches do not
establish exhaustive literature coverage, historical openness, or publication
priority.

The value 219781 is already known as a Fibonacci-type pseudoprime and is
listed in OEIS A094401, A093372, and A212424. That prior art is fully
attributed; no novelty or priority claim is made for its pseudoprime status.

## Route

Take `n=219781=271*811`. Kernel computation establishes
`Nat.fastFib 219781 mod 219781 = 1`, and `Nat.fastFib_eq` transports the result
to `Nat.fib 219781 mod 219781 = 1`. A `ZMod 219781` computation by
`reduce_mod_char`, followed by the natural-cast congruence, establishes
`2^219780 mod 219781 = 1`. Finally, `norm_num` proves that 219781 is not prime
from its factorization. Thus `inDetlefsSet(219781)` holds while
`Prime(219781)` does not, contradicting the universal biconditional.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. The
result instead supplies the two required residues at 219781 together with its
compositeness, producing `Not claim`.

## Evidence

- Lean module:
  `D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The profiled Lean process took 3.50 seconds wall time and 3.39 milliseconds
  of cumulative type checking, with maximum resident set size
  1,917,829,120 bytes.
- The finite certificate computes both residues at 219781 and proves
  `219781=271*811`; no private declaration is present.

Two independent Fibonacci residue computations, fast doubling and direct
iteration, both returned one at 219781. A bounded scan through one million
reported exactly seven composite values satisfying both tests:
219781, 252601, 399001, 512461, 722261, 741751, and 852841, with 219781 least.
The same scan reported that the prime 2 is the only prime outside the proposed
set in that range. It also reported that all seven composites satisfy the
May 28 congruence, including
`2^(3*219781) mod (3*219781) = 8` for the certified witness.

These bounded computations support the certified instance but do not assert
a classification of all counterexamples or a global least-counterexample
theorem.

## Triage

`theorem`. The finite certificate at the substantive composite 219781 refutes
the literal May 25 universal characterization. No claim is made about the
May 28 variant or the 2010 Wilson-type characterizations.

## ASSUMED-UNVERIFIED

The inaccessible older OEIS revision history, the bounded scans beyond the
single kernel-certified instance, and literature completeness beyond the
checked OEIS, arXiv, OpenAlex, MathOverflow, and GitHub surfaces are
`ASSUMED-UNVERIFIED`.
