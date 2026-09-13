---
slug: oeis-a018800-least-prime-prefix-suffix-refutation
bibkey: murthy2002a018800
doi: null
url: https://oeis.org/A018800
triage: theorem
motivation_gids:
  - D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation
---

# Refutation of the A018800 least-prime prefix suffix-bound conjecture

## Problem

OEIS A018800, NAME (verbatim):

> Smallest prime that begins with n.

COMMENTS conjecture line (verbatim; Amarnath Murthy, May 01 2002):

> Conjecture: If a(n) = (n concatenated with k) then k < n. - _Amarnath Murthy_, May 01 2002

The AUTHOR line is:

> _David W. Wilson_

The sequence begins
`11, 2, 3, 41, 5, 61, 7, 83, 97, 101, 11, 127, 13, 149, 151, 163, 17, 181, 19, 2003, 211, ...`.
For a natural number `n`, the formal sequence value is
`a(n) = sInf {p : Nat | Prime(p) and exists m : Nat, n * 10^m <= p and p < (n + 1) * 10^m}`.
The interval is the decimal-prefix reading of "begins with n". The literal
refuted statement is
`for all n >= 1, m >= 1, k < 10^m, a(n) = n * 10^m + k -> k < n`.
The condition `m >= 1` discloses the nonempty-suffix reading of
"n concatenated with k".

The existence of `a(n)` in general, the FORMULA line
`a(n) = prime(A085608(n))`, and an equivalence between the interval encoding
and a `Nat.digits` formulation are not claimed.

## Motivation

Murthy's 2002 comment states a universal strict bound on every appended
suffix. A certified counterexample at the first sequence index resolves that
literal conjecture without requiring a general existence theorem for the
sequence.

## Gap

Preregistration issue #7625 and its probe report record searches dated
September 14, 2026. The conjecture first appears in OEIS revision #4 dated
May 16, 2003; revision #74 dated August 18, 2026 still marks it as a
conjecture. Sloane's November 14, 2014 note proves only that a prefix prime
exists. Exact searches returned 0 results on Crossref, 0 on arXiv, 0 on the
MathOverflow API, and 0 on GitHub for the exact phrase. The OEIS Open paper
arXiv:2608.11941 had no metadata result for this conjecture. Loogle and
LeanSearch returned 0 relevant declarations. Google Scholar was unusable and
Semantic Scholar returned HTTP 429 to the search seat. OpenAlex returned HTTP
429 and a browser challenge; that surface is `ASSUMED-UNVERIFIED`.

This is an endpoint failure at the first index. The bounded searches do not
establish exhaustive literature coverage or publication priority.

## Route

The number 11 belongs to the defining prefix-prime set for `n = 1`: it is
prime and satisfies `10 <= 11 < 20` with `m = 1`. Every member of that set is
at least 11. When its interval exponent is zero, the only possible value is
1, which is not prime; when the exponent is positive, the interval lower
bound is at least 10, and primality excludes 10. These two bounds give
`a(1) = 11` by the natural infimum characterization. Instantiating the claim
at `n = m = k = 1` then requires `1 < 1`, a contradiction.

## Falsifier

A proof of the literal suffix bound for every `n >= 1`, every nonempty suffix
length `m`, and every `k < 10^m` would falsify this refutation. The
kernel-checked equality `a(1) = 11 = 1 * 10 + 1` makes such a proof imply the
false inequality `1 < 1`.

## Evidence

- Lean module:
  `D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.lean`.
- Main theorem: `result : not claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- On the stamped hot tree at the phase-A source, the profiled Lean process
  exited 0 in 6.86 seconds wall time, reported 10.5 milliseconds of cumulative
  type checking, and reached 1,515,257,856 bytes maximum resident set size.
- The orchestrator independently sieved primes through `6 * 10^7`. It matched
  the first 15 published terms and found that `n = 1` was the only violation
  for `1 <= n <= 5000`.
- The probe independently repeated the sieve and matched the first 21
  published terms:
  `11, 2, 3, 41, 5, 61, 7, 83, 97, 101, 11, 127, 13, 149, 151, 163, 17, 181, 19, 2003, 211`.

The bounded computations beyond `n = 1` are supporting evidence only. The
formal result uses the single counterexample at `n = 1`. It does not prove
general existence of `a(n)`, the FORMULA identity with A085608, a
`Nat.digits` equivalence, or a stronger suffix bound.

## Triage

`theorem`. The certified identity `a(1) = 11` refutes the literal universal
suffix-bound conjecture at its first index.

## ASSUMED-UNVERIFIED

OpenAlex was rate-limited behind a browser challenge. The literature search
is bounded and does not establish exhaustive coverage or publication
priority. The sieve results beyond the kernel-checked instance `n = 1` are
numerical evidence and are not formalized here.
