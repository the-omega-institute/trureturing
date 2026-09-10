---
slug: oeis-a387319-multiple-of-three-coincidence
bibkey: oeis2026a387319
doi: null
url: https://oeis.org/A387319
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/MultipleOfThreeCoincidence
---

# Multiple-of-Three Residue Coincidences

## Problem

OEIS A387319, revision 69 (November 10, 2025), conjectures that every
composite k except 4, 8, 10, and 25 has a coincidence between m=3 and
another multiple of 3 among the rational fractions (2k mod m)/m for
1≤m≤k, whereas no prime does. The exact predicate is
`∃ m : ℕ, 6 ≤ m ∧ m ≤ k ∧ 3 ∣ m ∧ 3*((2*k)%m) = m*((2*k)%3)`.
The theorem states that this is equivalent to
`1 < k ∧ ¬Nat.Prime k ∧ k ∉ ({4,8,10,25} : Finset ℕ)` for every natural k.

## Motivation

This is a first-tier recent OEIS comment conjecture. The caller selected it
from the dispatch entries of the September 9 triage and independently
checked the exact classification through k=3000. The finite observation
motivates a proof with no cutoff. Zero-valued coincidences are part of the
source condition, so multiples of three must not be discarded.

## Gap

The initial bind-only probe leaves the complete equivalence unresolved.
Pinned Mathlib supplies prime factorization, the least-prime-factor bound
and coprimality cancellation, but the inspected declarations do not give
this residue characterization or the bounded divisor construction.
The Library note records the direct-reference verification and the new
second-layer sources inspected; no target proof was located there.
Conjectural restatements remain conjectures, not published proofs.

## Route

Write m=3t. The equality holds exactly when t divides 2k and
`(2k/t)%3=(2k)%3`, with 2≤t and 3t≤k. In particular any admissible divisor
congruent to 1 modulo 3 works. For 3|k use t=2. For even k with 3 not
dividing k, the nonexceptional composite condition implies k≥12, so t=4
works. In the odd case write k=pq with p the least prime divisor.
Then q≥p≥5; use t=p if p%3=1 and t=2p if p%3=2. For the latter choice,
q<6 would force p=q=5 and k=25, which is excluded.

For prime k, t<k implies t coprime to k. From t|2k follows t|2, hence t=2.
The quotient residue condition then forces 3|k, inconsistent with prime k
and k≥6. Directly inspect the bounded moduli for the four exceptions.
All arithmetic in the classification is natural-valued and subtraction-free.
The only variable division in the proof has a divisor t≥2. The documentary
fraction formulation uses rational, not natural, division.

## Falsifier

A prime admitting an eligible modulus, any of the four exceptions admitting
one, or a nonexceptional composite with no eligible modulus would refute
the classification. A divisor t satisfying the stated bounds and quotient
residue but failing the original cross product would refute the bridge.
The empty search intervals at k=0 and k=1 are explicitly covered.

## Evidence

The sole public theorem is `MultipleOfThreeCoincidence.classify` in
`D5/S3/Arith/Congruence/MultipleOfThreeCoincidence.lean`. The complete
module compiled without diagnostics in the prior fragment-2b.log and in
the continuation's fresh-module.log. The continuation's `make lean` also
passed after serial cache completion. Its symbol audit confirms the
criterion dependencies and the standard three-axiom closure. The canonical
report passed with one added/rechecked module; ledger alignment added one
frozen module with zero conflicts. Scribe emission passed after repairing
an inherited formula-token spacing error. Exact report and frozen identities
are recorded in the Library note and implementation result.

Caller-provided reading: independently enumerated every k=1..3000, with
zero differences between Coincides and the classification. Triage-worker
report: independently enumerated k=1..5000 with zero differences.
The first implementation worker independently enumerated k=0..5000 using a
prime sieve and the original cross product, with zero differences. It also
tested the divisor/quotient criterion for all 2≤t≤k/3, with zero differences.
These three reports have separate provenance. The continuation worker
independently repeated k=0..5000 with trial-division primality and checked
4,160,835 eligible divisor pairs: zero differences on both checks.

Nonempty positive example: k=14, m=12 gives (28 mod 12)/12=4/12=1/3,
and (28 mod 3)/3=1/3. Both Coincides and the classification are true.
Negative example: k=13 is prime and its fractions at m=6,9,12 are
1/3, 8/9, 1/6; none equals the value 2/3 at m=3. Both sides are false,
and the composite premise is violated. The genuine exception k=25 is
composite, but its fractions at m=6,9,12,15,18,21,24 are respectively
1/3, 5/9, 1/6, 1/3, 7/9, 8/21, 1/12, never 2/3. At k=6 the values at
m=3 and m=6 are both 0, and both predicates are true. k=0,1 are false
on both sides. These values were actually calculated using exact fractions.

## Triage

`theorem`: the unbounded classification is implemented with no added
hypotheses. `proof_shape: content`; proposed module admission basis is
`escape-witness`. The criterion and explicit bounded divisor construction
are on the live proof path. The Library note distinguishes the kernel
result from source fidelity and the limited literature investigation.

## ASSUMED-UNVERIFIED

No exhaustive literature search, absence of proofs everywhere, novelty,
priority, independent review, or multi-model consensus is claimed. The
Anderson--Frazier paper was blocked and not read; the full reference graph
of doubled primes was not traversed. The caller and triage enumeration
ranges above are attributed reports, not this worker's execution receipts.
The inherited Lean proof and documentation are explicitly distinguished
from the continuation's own source reading, binding probe, exact-fraction
controls, and numerical checks in the Library note. Prior fragment-log
success is inherited evidence; fresh kernel and repository gate receipts
are reported separately there. Neither implementation worker constitutes
an independent review of its own work.
The source's separate first-coincidence observation and A343311 equality
conjecture are not claimed proved. Full local preflight and unrelated
tool tests are not claimed run. Source-to-definition fidelity and the
four escape-witness criteria require semantic review; the kernel proves
the explicit Lean statement. Numerical checks do not prove the theorem.
