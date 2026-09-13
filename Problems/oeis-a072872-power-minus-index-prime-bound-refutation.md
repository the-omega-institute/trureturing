---
slug: oeis-a072872-power-minus-index-prime-bound-refutation
bibkey: cloitre2002a072872
doi: null
url: https://oeis.org/A072872
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation
---

# Refutation of the A072872 prime-index upper-bound conjecture

## Problem

OEIS A072872, NAME (verbatim):

> a(n) is the smallest positive number k such that n divides 2^k - k

COMMENTS (verbatim; Benoit Cloitre, Jul 28 2002):

> If n is a power of 2, a(n) = n. Conjecture : if n > 47, a(n) < prime(n). - _Benoit Cloitre_, Jul 28 2002

The literal claim is `∀ n > 47, a(n) < prime(n)`, where `prime(n)` is the
n-th prime. The formal definition uses
`a(n) = sInf {k ∈ ℕ | 0 < k ∧ n ∣ 2^k - k}` and discloses the convention
`sInf ∅ = 0`; no general existence claim for this set is made.

## Motivation

This first-tier OEIS conjecture was printed in 2002 and is a universal bound
on the least positive exponent satisfying the power-minus-index divisibility
condition. A certified counterexample resolves the literal bound without
proposing a corrected statement.

## Gap

Preregistration issue #7480 and its probe report record the bounded literature
searches. OEIS history revisions #1 through #14 only restate or reword the
sequence and conjecture. Searches of arXiv, OpenAlex, and MathOverflow returned
0 results for the exact claim. GitHub returned implementations and sequence
mirrors only. The sibling OEIS A247248, using `2^k + k`, has an IMO existence
proof; that existence result concerns a different sequence and does not address
the A072872 prime-index bound. These checked surfaces do not establish
exhaustive literature coverage or publication priority.

## Route

At `n = 6298`, the endpoint certificate proves
`6298 ∣ 2^77742 - 77742`, and the incremental residue certificate proves that
no positive `k < 77742` satisfies the same divisibility. Therefore
`a(6298) = 77742`. The chunked trial-division and prime-count certificate,
using `Nat.nth_count`, proves `p₆₂₉₈ = 62753`. Since `77742 ≥ 62753`, the
universal strict upper bound fails.

## Falsifier

A proof of `∀ n > 47, a(n) < prime(n)` would falsify this refutation. The
kernel-checked instance at `n = 6298` proves the opposite inequality for that
input, so such a proof would contradict `result`.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/CloitrePowerMinusIndexPrimeBoundRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms `propext`, `Classical.choice`, and `Quot.sound`.
- The per-step kernel readings in the probe report cover endpoint membership, incremental residue minimality for `k < 77742`, and the chunked prime-count certificate. The orchestrator independently ran the modular loop and sieve; the probe ran the same checks and found no counterexample for `48 ≤ n < 1500`.

## Triage

`theorem`. The certified instance at `n = 6298` refutes the universal
prime-index upper bound. It asserts no corrected bound and no claim about
other values of `n`.

## ASSUMED-UNVERIFIED

- The literature search is bounded to the recorded OEIS, arXiv, OpenAlex, MathOverflow, GitHub, and sibling-sequence surfaces; no exhaustive coverage or publication-priority claim is made.
- `6298` is not claimed to be the least counterexample.
- Nonemptiness of the defining set is not claimed for every natural `n`.
