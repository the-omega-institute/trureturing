---
slug: oeis-a249621-square-prepend-one-append-twenty-five
bibkey: wu2014a249621
doi: null
url: https://oeis.org/A249621
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive
---

# OEIS A249621 terminal digits for square concatenations

## Problem

OEIS A249621 %N:

> Squares that remain squares when prepended with 1 and appended with 25 in base 10.

OEIS A249621 %C:

> Conjecture: all the numbers in the sequence end in either 00 or 56.

— _Chai Wah Wu_, Nov 02 2014.

For a natural number `x`, membership means that `x` is a square and, if `d` is
the number of its base-ten digits, then `10^(d+2) + 100x + 25` is also a square.
This is the literal base-ten concatenation `1||x||25`.

## Motivation

This 2014 OEIS conjecture asks for the terminal two digits of every positive
square whose decimal prefix and suffix preserve squareness. The formal result
settles the stated terminal-digit alternative for all positive members.

## Gap

The dated surfaces recorded in preregistration issue #7463 and its probe report
were checked on 2026-09-13. The OEIS family entries only restate the conjecture;
OpenAlex, Crossref, DataCite, MathOverflow, and Math.StackExchange returned 0
exact-identifier results. arXiv was not verified (export API HTTP 429 on
2026-09-13); this reading is ASSUMED-UNVERIFIED. GitHub returned mirrors only.
This is a bounded literature search and does not establish exhaustive coverage.

## Route

From `y^2 = 10^(d+2) + 100x + 25`, reduction modulo 100 gives `5 | y`.
Write `y = 5u` and `x = z^2`. For `d >= 2`, the leading power of ten vanishes
modulo 10000; cancelling 25 reduces the equation to
`u^2 = 4z^2 + 1 (mod 400)`. Complete residue classification modulo 25 and
modulo 8 forces `z^2 mod 100` to be 0 or 56. The small cases `x < 100` are
excluded directly in the proof.

## Falsifier

A single positive member whose final two decimal digits are neither 00 nor 56
would falsify the theorem. A failure of the residue classification or of the
small-case exclusion would also invalidate the proof route.

## Evidence

- Lean module: `D5/S1/Digit/Admissibility/SquarePrependOneAppendTwentyFive.lean`.
- Main theorem: `wu_a249621`; public definition: `IsMember`.
- The private residue lemma gives the complete classification modulo 400.
- The theorem and definition have the std3 axiom closure.
- The orchestrator checked all 27/27 b-file terms and a k-parametrized search
  through `d <= 14`, finding only `81390384100`; the residue classification was
  checked separately.
- The probe searched `z <= 10^6` and found one member.

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

None beyond the bounded literature search and the numerical checks described
above. The source quotation, attribution, and source-to-Lean identification are
documentary evidence; the Lean kernel checks the formal statement.
