---
slug: oeis-a343502-divisor-count-primes-dequatre
bibkey: dequatre2021a343502
doi: null
url: https://oeis.org/A343502
triage: theorem
motivation_gids:
  - D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes
---

# Dequatre's OEIS A343502 divisor-count prime conjecture

## Problem

C. H. R. Dequatre's OEIS A343502 is titled “Numbers k such that tau(tau(k)) and tau(k+1) are both prime, where tau is the number of divisors function.” Its comment states: “Conjecture: all members except 2 and 3 are composite.” The entry also asks whether there are finitely many odd terms.

The formal claim is that every natural number $k$ with $1 \le k$, with both divisor-count conditions prime, and with $k \ne 2$ and $k \ne 3$, satisfies $1 < k$ and is not prime.

### Statement echo

The membership predicate in `D5/S3/Arith/Divisors/OeisA343502DivisorCountPrimes.lean` expands tau literally as `k.divisors.card`, preserving the source convention. The settling declaration is `result : claim`; its Scribe formula expands the complete claim body.

## Motivation

The conjecture isolates the only prime members visible in the published data and would explain the observed composite tail. A proof also reduces the remaining odd-term question to a more specific divisor-count problem without claiming that question is solved.

## Gap

OEIS A343502 revision 27 presents the assertion as a conjecture and gives no proof. The preregistered literature screen in issue [#18685](https://github.com/the-omega-institute/trureturing/issues/18685) found no proof in the searched OEIS, formal-conjecture, and repository sources. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Assume a member $k \ne 2,3$ is prime. Then $k$ is odd, so $k+1$ is even. The prime value of the divisor count of $k+1$ forces all prime factors of $k+1$ to equal $2$, hence $k+1=2^e$ and its divisor count is $e+1$. The primality of $k=2^e-1$ makes $e$ prime; the primality of $e+1$ then forces $e=2$, giving $k=3$, a contradiction. The proof also derives $1<k$ from the membership condition.

## Falsifier

A prime member other than $2$ or $3$, or a failure of the prime-power reduction for an even $k+1$, would falsify the settlement. The independent finite check is evidence for the stated range only and does not replace the universal proof.

## Evidence

The kernel-checked settling declaration is `D5.S3.Arith.Divisors.OeisA343502DivisorCountPrimes.result`. Its proof uses the frozen divisor-factor bound `D5.S3.Arith.DivisorCountRadicalCoincidence.primeFactors_card_le_cardFactors_card_divisors` and the frozen divisor-count owner through the consumed correspondence lemma. The public result's axiom closure is contained in `{propext, Classical.choice, Quot.sound}`.

The numerical check is preserved in the experiments repository at [`docs/reports/oeis-a343502-divisor-count-primes`](https://github.com/the-omega-institute/trureturing-experiments/tree/7fdb3ba9193467aed2f82d68b1849973befe4a48/docs/reports/oeis-a343502-divisor-count-primes). Running `python3 check.py 2000000` exits 0 and reports 37181 members through 2,000,000, with prime members exactly 2 and 3; the script SHA-256 is `57e9715d1209fafdf2d9090b4f1c3fa1f100069d45288e92e018d266f653f3c3`.

The escape audit for the settling result and the published owner theorem is unfinished and tracked in [#19974](https://github.com/the-omega-institute/trureturing/issues/19974); no `declared_validated` registration is claimed.

## Triage

| target item | status | evidence |
| --- | --- | --- |
| Settlement of Dequatre's conjecture | proved | Kernel-checked `D5.S3.Arith.Divisors.OeisA343502DivisorCountPrimes.result` |
| Tier 1 explicit OEIS conjecture | proved | Source statement and preregistration in [#18685](https://github.com/the-omega-institute/trureturing/issues/18685) |
| Implement the single settlement module and matching artifacts | proved | The settling module, Scribe, Library note, dossier, and frozen state are present at their canonical paths |
| Whether A343502 has finitely many odd terms | open | The source's separate question is not asserted by `result` |
| Even prime-divisor-count reduction for $k+1$ | proved | Local propositions in the proof of `result`; no standalone general prime-power theorem is delivered |

### What the settlement shows

**Proved by `result`.** Every A343502 member other than 2 and 3 is composite, with the exact universal quantifiers and divisor-count convention in the source claim.

**Proved mechanism.** For a hypothetical prime member, parity makes $k+1$ even; the prime divisor count collapses its prime-factor set to `{2}`, giving a power of two. The two adjacent prime conditions force the exponent to be 2, which is exactly the excluded member $k=3$.

**Scope.** The argument settles the conjecture for all natural $k$ under the stated membership predicate. It does not determine whether the sequence has finitely many odd terms.

**Effect on the source.** The OEIS conjecture is resolved as proved. The separate odd-term question remains open.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `D5.S3.Arith.Divisors.OeisA343502DivisorCountPrimes.result` | bind-only after helper expansion | none | open-problem-resolution (#18685; Proved) |
| `D5.S3.Arith.DivisorCountRadicalCoincidence.primeFactors_card_le_cardFactors_card_divisors` | bind-only | none | published-owner consumed dependency; escape audit unfinished in #19974 |

## ASSUMED-UNVERIFIED

The literature search establishes only the bounded scope recorded in issue #18685; exhaustive worldwide completeness and priority remain `ASSUMED-UNVERIFIED`. The separate finiteness question for odd terms is open.
