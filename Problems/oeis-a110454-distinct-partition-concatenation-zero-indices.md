---
slug: oeis-a110454-distinct-partition-concatenation-zero-indices
bibkey: murthy2005a110454
doi: null
url: https://oeis.org/A110454
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite
---

# The zero indices of A110454

## Problem

OEIS A110454, NAME (verbatim):

> Largest composite number obtained by concatenation of parts of a distinct partition of n, or 0 if no such number exist.

COMMENT (verbatim; Amarnath Murthy, Aug 04 2005):

> Conjecture a(n) = 0 only for n = 1, 2 and 4.

The Maple program by R. J. Mathar, dated Feb 08 2008, examines every
permutation of every distinct partition and accepts a concatenation exactly
when `m > 4` and `m` is not prime. Its loop includes single-part partitions.

## Motivation

The conjecture identifies every positive index where the admissible set is
empty. A proof therefore requires both an unbounded construction away from
the three exceptional indices and finite exclusion at `1`, `2`, and `4`.

## Gap

The dated search recorded on 2026-09-13 checked the OEIS entry and all 11
revisions, arXiv by identifier, OpenAlex full text, MathOverflow advanced
search, GitHub issues, commits, and repositories outside this repository,
Loogle, and LeanSearch. A proof or counterexample was not found in the
checked surfaces. GitHub code-content search, Google Scholar, and MathSciNet
were not checked. This bounded search is not an exhaustive literature or
priority claim.

## Route

At `n = 3`, the ordered distinct partition `[2,1]` gives the concatenation
`21`, which is greater than four and composite. For every `n >= 5`, the
ordered distinct partition `[n-2,2]` gives
`10(n-2)+2 = 2(5n-9)`, again greater than four and composite. The remaining
positive indices are `1`, `2`, and `4`; direct classification of their
distinct partitions shows that none of their concatenations is both greater
than four and composite.

## Falsifier

A positive `n` outside `{1,2,4}` for which every distinct-partition
concatenation greater than four is prime would contradict the first
conjunct. An admissible composite concatenation at any of `1`, `2`, or `4`
would contradict the second conjunct.

## Evidence

- Lean module: `D5/S1/Digit/Admissibility/DistinctPartitionConcatenationComposite.lean`.
- Main theorem: `murthy_conjecture`.
- Public definitions: `decimalConcatenation` and `C`.
- The theorem's axiom closure is exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- The exact check recorded by the orchestrator enumerated all distinct
  partitions and their permutations for `1 <= n <= 35`; its values matched
  the OEIS DATA at every index, and its zero indices were exactly `1`, `2`,
  and `4`.

## Triage

`theorem`. The formal proof establishes both the universal existence clause
outside the three exceptions and the complete finite exclusion clause at
the exceptions.

## ASSUMED-UNVERIFIED

The revision-history and literature-search report is evidence recorded in
the preregistration issue and was not independently repeated here. The
enumeration through `n = 35` is an orchestrator-supplied exact check, not a
kernel proof. Source-to-Lean identification is not itself kernel checked.
No exhaustive literature or first-publication priority claim follows.
