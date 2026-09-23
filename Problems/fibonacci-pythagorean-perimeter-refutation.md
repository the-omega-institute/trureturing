---
slug: fibonacci-pythagorean-perimeter-refutation
bibkey: huber2023a134492
doi: null
url: https://oeis.org/A134492
triage: theorem
motivation_gids:
  - D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result
---

# Fibonacci Numbers That Are Pythagorean Perimeters

## Problem

OEIS A134492 is the sequence `a(n) = Fibonacci(6n)`. Its COMMENTS section carries,
at revision #62 of Sep 22 2025:

> Conjecture: For n >= 2, the terms of this sequence are exactly those Fibonacci
> numbers which are the sum of the three numbers of a Pythagorean triple (checked
> up to F(80)). - _Felix Huber_, Nov 03 2023

With quantifiers written out, and `P(N)` for `∃ a b c > 0, a² + b² = c² ∧ a + b + c = N`:

    ∀ N, (∃ k, F(k) = N) → (P(N) ↔ ∃ n ≥ 2, F(6n) = N).

The comment says "a Pythagorean triple" with no qualifier, so the triples are all
triples of positive integers, primitive or not.

## Motivation

The frozen theorem
`D5/S3/Arith/FibonacciPythagoreanPerimeterRefutation.result` refutes it.

## Gap

Issue 9430 records the screen carried out before the probe. The entry was read in
full at revision #62: the conjecture stands unqualified, with no counterexample and
no proof recorded. A web pass over the sequence number together with the terms of
the conjecture returned nothing. Citation indices were not exhaustively reachable,
so this is a bounded negative finding.

## Route

Every Pythagorean triple is `d` times a primitive one with parameters `m > n ≥ 1`,
`gcd(m, n) = 1`, `m - n` odd, so its perimeter is `2 d m (m + n)`. Writing `s = m`
and `t = m + n`, the perimeters are exactly the numbers `2 s t d` with `s < t < 2s`,
`gcd(s, t) = 1` and `t` odd. So `N` is a perimeter precisely when `N` is even and
`N/2` has a factorisation `s · t · d` of that shape.

Two consequences fix where the conjecture can fail. First, perimeters are even, so a
Fibonacci number at an index not divisible by three, being odd, is never one; those
indices agree with the conjecture for trivial reasons. Second, at an index divisible
by three the question becomes whether `F(k)/2` admits a pair of coprime divisors
`s < t < 2s` with `t` odd — a question about how the divisors of `F(k)` are spaced,
with no reason to answer no once `F(k)` has enough prime factors.

Running that test over the indices divisible by three finds the first failure at
index forty-five. `F(45) = 1134903170`, `F(45)/2 = 61 · 85 · 109441`, and the
parameters `s = 61`, `t = 85`, that is `m = 61`, `n = 24`, give the primitive triple
`(3145, 2928, 4297)`. Scaling by `109441`:

    344191945² + 320443248² = 470267977² ,
    344191945 + 320443248 + 470267977 = 1134903170 = F(45) .

Forty-five is not a multiple of six, and `F(45)` is not a term of the sequence
because `F(42) = 267914296 < 1134903170 < 4807526976 = F(48)` and `Nat.fib` is
monotone. The recorded proof carries only the triple and that monotonicity step; the
divisor analysis above is how the triple was found, not part of the proof.

## Falsifier

A different value for `F(45)`, or an arithmetic slip in the triple, would invalidate
the witness; both are checked by the kernel. The witness does not depend on the
parametrisation of Pythagorean triples: it is three explicit positive integers whose
squares and whose sum are computed directly.

## Evidence

Forty-five is the smallest counterexample. At indices not divisible by three the
Fibonacci numbers are odd and hence not perimeters, matching the conjecture; at the
indices `3, 6, ..., 42` divisible by three the conjecture holds. Further failures of
the same kind occur at indices `57, 63, 69, 75, 81`.

The counterexample lies inside the range the comment reports having checked, `F(80)`.
Under the alternative reading that restricts the triples to primitive ones the
conjecture also fails inside that range: `F(18)` and `F(54)` are terms of the
sequence but are not perimeters of primitive triangles, and `F(81)` is one without
`81` being a multiple of six. So no reading of the comment survives its own stated
verification range.

## Triage

`theorem`; Tier 1 named external conjecture on an OEIS comment line, preregistered in
issue 9430 before the probe. The admission basis is `open-problem-resolution`; the
conservative classification is `proof_shape: bind-only` with `escape_witness: none`,
since the proof is one certified witness together with monotonicity of `Nat.fib`. The
computational use is a `certified-instance` with a typed `refutes` edge from `result`
to `claim`.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the OEIS entry at revision #62 and a web pass over
the sequence number and the conjecture's terms were opened; citation-index result
pages were not exhaustively reachable, so no worldwide priority claim is made.

The further failing indices `57, 63, 69, 75, 81` and the primitive-reading failures at
`18, 54, 81` were found by the divisor test described above and are not part of the
recorded proof; they are reported as computation, not as kernel-checked facts.
