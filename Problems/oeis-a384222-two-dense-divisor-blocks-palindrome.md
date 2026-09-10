---
slug: oeis-a384222-two-dense-divisor-blocks-palindrome
bibkey: pol2025a384222
doi: null
url: https://oeis.org/A384222
triage: theorem
motivation_gids:
  - D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome
---

# Palindromic composition of the A384222 rows

## Problem

> Conjecture 1: row n is a palindromic composition of A000005(n).

— Omar E. Pol (entry Jun 03 2025), OEIS A384222.

The defining comments supplied with the conjecture are:

> The 2-dense sublists of divisors of n are the maximal sublists whose terms increase by a factor of at most 2.

> In a sublist of divisors of n the terms are in increasing order and two adjacent terms are the same two adjacent terms in the list of divisors of n.

For positive n, the row lists the lengths of these maximal consecutive blocks;
A000005(n) is the number of positive divisors, τ(n).

## Motivation

This is the first-tier recent OEIS conjecture selected in the implementation
brief. The KPI is open problems resolved. The target is the entire conjecture
for every positive n, not a finite range of rows.

## Gap

The supplied search-seat report found no proof in the OEIS entry and revision
history read on 2026-09-08, or in identifier searches on arXiv, MathOverflow,
and GitHub. This Stage-B seat had no network access and did not independently
repeat those searches. This is a report of no proof found in the searched
scope, not an exhaustive assertion about the literature.

## Route

For positive n, the involution d ↦ n/d reverses the ordered positive-divisor
list. For divisors d,e it preserves the cut condition
e ≤ 2d ⟺ n/d ≤ 2(n/e). Thus both links inside a maximal block and cuts between
blocks are preserved after reversing order. The private `split_reverse_map`
lemma constructs the reversed mapped decomposition and uses `splitBy`
uniqueness to identify it, block by block. Taking lengths gives a palindrome.
Flattening the nonempty blocks recovers the full divisor list, so their lengths
are positive and sum to τ(n). The public companion `row_sum` proves the sum;
positivity follows from the nonempty-block contract of `List.splitBy`.

## Falsifier

A positive counterexample index n whose maximal two-dense divisor-block
lengths fail to be a palindrome or a composition of τ(n) would refute the
assertion. The orchestrator's exact numerical check is supporting evidence
only; no finite check proves the unbounded statement.

## Evidence

- Lean module: `D5/S3/Factorization/TwoDenseDivisorBlocksPalindrome.lean`.
- Main public theorem: `row_palindrome`.
- Companion public theorem: `row_sum`.
- Both theorems have axioms std3: `propext`, `Classical.choice`, `Quot.sound`,
  as printed by the Stage-B single-file Lean check (exit 0).
- The single-file Lean check and header-check both returned exit 0 after
  removal of the finite regression. The proof quantifies over every positive n.

## Triage

`theorem`. The formal palindrome and sum assertions, together with the
nonempty blocks in the row definition, close the supplied OEIS conjecture.

## ASSUMED-UNVERIFIED

The verbatim quotes and attribution were supplied by the orchestrator. The
OEIS entry and revision history were read by the search seat on 2026-09-08,
not by this seat. The reported literature scope was identifier search on
arXiv, MathOverflow, and GitHub, alongside that OEIS reading; this seat had no
network access. First-publication priority, exhaustive absence of another
proof, and source-to-Lean identification are not kernel-checked facts.
