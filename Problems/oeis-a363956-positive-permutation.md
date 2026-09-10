---
slug: oeis-a363956-positive-permutation
bibkey: shannon2023a363956
doi: null
url: https://oeis.org/A363956
triage: theorem
motivation_gids:
  - D5/S3/Arith/OmegaGreedyPermutation
---

# The permutation conjecture for A363956

## Problem

> The sequence is conjectured to be a permutation of the positive integers.

The sequence begins with 1 and 2. Thereafter take the smallest positive unused
multiple of the omega-th prime, where omega counts distinct prime factors of
the previous term.

## Motivation

This Tier 1 OEIS conjecture is asymptotic. Missing primes in a finite prefix
do not decide it. The task is surjectivity of the actual greedy recursion.

## Gap

The main entry and one-hop A363504/A351495 entries were read on 2026-09-10;
each states its permutation claim as a conjecture without a proof. Bounded
repository, pinned Mathlib, GitHub Lean-code and arXiv searches found no proof
of the target claim. These searches do not establish priority.

## Route

Infinitely activated queues exhaust all positive multiples. Finiteness of the
queue-2 activations would make the entire prime-output set finite, hence all
selected queues finite in number. One infinite queue then forces unbounded
distinct-factor counts, contradiction. The resulting coverage of even numbers
forces every prime queue by varying the exponent of 2 at fixed prime support.

## Falsifier

A positive integer proved to be absent would refute surjectivity. A proof
that some prime queue is activated only finitely often would contradict the
stronger intermediate result. Finite prefix omissions provide neither witness.

## Evidence

D5/S3/Arith/OmegaGreedyPermutation.lean proves sequence_initial,
sequence_positive, sequence_injective, sequence_greedy and a363956_surjective.
The definition uses a finite used-set recursion and a natural infimum. Fairness
and surjectivity are derived, never assumed. Kernel and repository build
receipts are in docs/reports/a363956-0910.md.

## Triage

theorem. The full positive-integer permutation question is answered by
unbounded proofs of surjectivity and injectivity.

## ASSUMED-UNVERIFIED

Linked data, plots and revision histories were not opened. No assertion is
made about rates, fixed points or the multiplicity-count variant A363504.
The match between the Lean rule and OEIS prose is a source-fidelity assessment.
