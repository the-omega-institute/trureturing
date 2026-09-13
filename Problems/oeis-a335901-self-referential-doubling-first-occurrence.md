---
slug: oeis-a335901-self-referential-doubling-first-occurrence
bibkey: alkan2020a335901
doi: null
url: https://oeis.org/A335901
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence
---

# First Occurrences in OEIS A335901

## Problem

OEIS A335901, %N (verbatim):

> a(n) = 2*a(floor((n-1)/a(n-1))) with a(1) = 1.

%C (verbatim):

> Least k such that a(k) = 2^n are 1, 2, 5, 21, 169, 2705, ... (Conjecture: This sequence is A117261).

The comparison sequence A117261 is given by A117261(0) = 1 and
A117261(r+1) = 2^r * A117261(r) + 1. The phrase "least k such that
a(k) = 2^r" is formalized as a hit together with minimality among positive
indices.

## Motivation

The conjecture identifies the first occurrence of every power of two in a
self-referential recurrence with a named OEIS sequence. A proof settles the
conjecture and records the resulting open-problem resolution.

## Gap

The dated surfaces recorded from issue #7468 and the probe are: OEIS history
revision #4 introduces the conjecture, revision #5 rewords it, and revision
#16 leaves it unchanged. A117261 revision #18 does not mention A335901.
OpenAlex, Crossref, DataCite, arXiv, MathOverflow, and Math.StackExchange
searches returned 0 exact matches for the paired claim. GitHub code search for
both A-numbers returned 0 results. These are bounded search results, not an
exhaustive literature claim.

## Route

The proof establishes the block invariant: a(T(r)) = 2^r; for r >= 1 and
T(r) <= n < T(r+1), a(n) is either 2^(r-1) or 2^r; and if
a(n) = 2^(r-1), then n < 2^(r-1) * T(r). A two-step induction on r places the
recurrence quotient into one of the preceding two blocks. The hit occurs at
the block start, and the block bound supplies minimality.

## Falsifier

One natural r for which the least positive k with a(k) = 2^r differs from
T(r) would falsify the theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence.lean`.
- Main theorem: `alkan_a335901`; the theorem states the hit and minimality for every natural r.
- Definitions: `a` and `T`; the private block invariant is an internal proof component.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- Orchestrator recurrence to n = 3*10^6: first occurrences of 2^r for r = 0..6 are 1, 2, 5, 21, 169, 2705, 86561, and all observed values are powers of two.
- Probe to n = 6*10^6 reaches r <= 7, with the r = 7 first occurrence at 5539905; the b-file check reports 10000/10000.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

None beyond the bounded literature search described above.
