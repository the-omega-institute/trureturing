---
slug: oeis-a084068-pell-companion-gcd
bibkey: oeis2025a084068
doi: null
url: https://oeis.org/A084068
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/PellCompanionGcd
---

# The A084068 Pell gcd conjecture

## Problem

Joseph A. Stocke's July 28, 2025 conjecture in OEIS A084068 states
`A084068(n) = gcd(A001108(n), A001109(n))` for every n at least one.
The entry still labels this formula a conjecture when inspected on
September 8, 2026.

## Motivation

This is a first-tier recent OEIS conjecture. Define Pell numbers P by
P(0)=0, P(1)=1 and companion Pell numbers Q by Q(0)=Q(1)=1, both with
R(n+2)=2R(n+1)+R(n). The three OEIS entries explicitly identify the
conjecture with the parity-dependent gcd formula proved in the module.

## Gap

The implementation brief reports no independent published proof in its
searched public indexes. The missing argument is that P(n) and Q(n) are
coprime and Q(n) is odd for every index.

## Route

Induction converts the second-order recurrences into
P(n+1)=P(n)+Q(n), Q(n+1)=2P(n)+Q(n). This step preserves coprimality,
because gcd(p+q,2p+q)=gcd(q,p), and preserves oddness of Q.

For even n, gcd(2P(n)^2,P(n)Q(n)) equals
P(n)*gcd(2P(n),Q(n))=P(n). Oddness makes Q(n) coprime to 2, so
coprimality with P(n) implies coprimality with 2P(n).
For odd n, gcd(Q(n)^2,P(n)Q(n)) equals
Q(n)*gcd(Q(n),P(n))=Q(n).

## Falsifier

A positive index at which the normalized gcd differs from P(n) on the
even branch or Q(n) on the odd branch would contradict the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/PellCompanionGcd.lean`.
- Public theorem: `pell_companion_gcd`; it also holds at index zero.
- The source formulas were directly checked on all three OEIS pages;
  bibliographic details are in `Library/Arith/oeis2025a084068.md`.
- The formal result is unbounded in n; finite experiments are not its proof.

## Triage

`theorem`. The normalized universal assertion has a formal proof. The
other A084068 conjecture concerning A348295 is outside this result.

## ASSUMED-UNVERIFIED

First-publication priority is not established. The brief's absence-of-proof
search did not exhaust private or unindexed literature. The external OEIS
identifications were checked by reading the pages; they are not formal
theorems about the website. No claim of exhaustive literature search is made.
